// A fast, dependency-free Markdown renderer matching marked 18.1.3's HTML
// (default options: GFM on, breaks off, pedantic off). Written from scratch:
// a line-oriented block scanner that collects link reference definitions
// first, then a single-pass inline scanner that renders straight to HTML
// (no token tree, no second render pass). Correctness target is CommonMark
// 0.31.2 + GFM 0.29 as marked renders them; where marked departs from the
// spec, marked's output is what this reproduces.

// ---------- small shared helpers ----------

const ESC_MAP = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };

// Escape HTML. encode=true escapes every & < > " '; otherwise < > " ' are
// escaped and & only when it does NOT start a valid character reference.
function esc(s, encode) {
  if (encode) return s.replace(/[&<>"']/g, (c) => ESC_MAP[c]);
  return s.replace(/[<>"']|&(?!(?:#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g, (c) => ESC_MAP[c]);
}

// Decode numeric character references inside a text run (marked's unescape):
// &#65; / &#x41; -> the character, &#0; / surrogates / >0x10FFFF -> U+FFFD,
// &#38; -> "&amp;", a bare & (not starting a valid reference) -> "&amp;".
// Named references are left untouched.
const NUM_REF = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const NUM_REF_OR_BARE_AMP = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(?:#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;
function decodeRefs(s) {
  if (!NUM_REF.test(s)) return s;
  return s.replace(NUM_REF_OR_BARE_AMP, (m, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const cp = dec === undefined ? parseInt(hex, 16) : parseInt(dec, 10);
    if (cp === 0 || cp > 0x10ffff || (cp >= 0xd800 && cp <= 0xdfff)) return '\uFFFD';
    if (cp === 38) return '&amp;';
    return String.fromCodePoint(cp);
  });
}

// Encode a link href the way marked does: encodeURI, then %25 back to %.
function encodeHref(href) {
  try {
    return encodeURI(href).replace(/%25/g, '%');
  } catch {
    return null;
  }
}

// Normalize a link label for lookup: trim, collapse whitespace, fold case
// through lower -> upper -> lower (marked's F()).
function normLabel(s) {
  return s.trim().replace(/\s+/g, ' ').toLowerCase().toUpperCase().toLowerCase();
}

// Expand tabs to spaces, tracking the column (tab stops every 4).
function expandTabs(s, col = 0) {
  let c = col, out = '';
  for (const ch of s) {
    if (ch === '\t') {
      const n = 4 - (c % 4);
      out += ' '.repeat(n);
      c += n;
    } else {
      out += ch;
      c++;
    }
  }
  return out;
}

// Trim trailing blank lines from a block, keeping at most one trailing
// blank line (marked's ge()).
function trimTrailingBlanks(s) {
  const lines = s.split('\n');
  let t = lines.length - 1;
  while (t >= 0 && /^[ \t]*$/.test(lines[t])) t--;
  if (lines.length - t <= 2) return s;
  return lines.slice(0, t + 1).join('\n');
}

// Strip a trailing run of `ch` from s; if `alsoNon` also strip trailing
// characters that are not `ch`. (marked's L()).
function stripTail(s, ch, alsoNon) {
  let n = s.length, k = 0;
  while (k < n) {
    const c = s.charAt(n - k - 1);
    if (c === ch && !alsoNon) k++;
    else if (c !== ch && alsoNon) k++;
    else break;
  }
  return s.slice(0, n - k);
}

// Find the index of the first unbalanced closing paren in s, or -1 when
// balanced, -2 when there are unclosed opens (marked's ke()).
function parenBalance(s, pair) {
  if (s.indexOf(pair[0]) === -1 && s.indexOf(pair[1]) === -1) return -1;
  let depth = 0;
  for (let i = 0; i < s.length; i++) {
    if (s[i] === '\\') i++;
    else if (s[i] === pair[0]) depth++;
    else if (s[i] === pair[1]) {
      depth--;
      if (depth < 0) return i;
    }
  }
  return depth > 0 ? -2 : -1;
}

// ---------- regexes ----------
// Block-level tag names (CommonMark HTML block type 6).
const BLOCK_TAGS =
  'address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul';

const RE = {
  newline: /^(?:[ \t]*(?:\n|$))+/,
  indentedCode: /^((?: {4}| {0,3}\t)[^\n]+(?:\n(?:[ \t]*(?:\n|$))*)?)+/,
  fences:
    /^ {0,3}(`{3,}(?=[^`\n]*(?:\n|$))|~{3,})([^\n]*)(?:\n|$)(?:|([\s\S]*?)(?:\n|$))(?: {0,3}(?:(?=`)\1`*|(?=~)\1~*) *(?=\n|$)|$)/,
  hr: /^ {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/,
  atx: /^ {0,3}(#{1,6})(?=\s|$)(.*)(?:\n+|$)/,
  bullet: / {0,3}(?:[*+-]|\d{1,9}[.)])/,
  listStart: /^( {0,3}(?:[*+-]|\d{1,9}[.)]))((?:[ \t][^\n]*)?(?:\n|$))/,
  htmlComment: /<!--(?:-?>|[\s\S]*?(?:-->|$))/,
};

// When a regex source is spliced into another pattern, its `^` anchors are
// dropped (they would only ever match the start of the whole string, never
// a position after a newline) — the same rule marked's pattern builder uses.
const stripCaret = (s) => s.replace(/(^|[^\[])\^/g, '$1');
// Thematic-break pattern with no capture groups, for splicing into
// lookaheads (a capturing group there would renumber the groups after it).
const HR_NC = ' {0,3}(?:(?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)';

// Link reference definition label / title fragments.
const LABEL_INNER = String.raw`(?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+`;
const TITLE_INNER = String.raw`(?:"(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\\n]|\n(?!\n))*'|\((?:\\[\s\S]|[^()\\])*\))`;
RE.def = new RegExp(
  `^ {0,3}\\[(${LABEL_INNER})\\]: *(?:\\n[ \\t]*)?([^<\\s][^\\s]*|<.*?>)(?:(?: +(?:\\n[ \\t]*)?| *\\n[ \\t]*)((${TITLE_INNER})))? *(?:\\n+|$)`,
);

// HTML block (types 1-7).
const ATTR = ' +[a-zA-Z:_][\\w.:-]*(?: *= *"[^"\\n]*"| *= *\'[^\'\\n]*\'| *= *[^\\s"\'=<>\\x60]+)?';
RE.htmlBlock = new RegExp(
  '^ {0,3}(?:<(script|pre|style|textarea)[\\s>][\\s\\S]*?(?:</\\1>[^\\n]*\\n*|$)' +
    '|<!--(?:-?>|[\\s\\S]*?(?:-->|$))[^\\n]*(\\n+|$)' +
    '|<\\?[\\s\\S]*?(?:\\?>[^\\n]*\\n*|$)' +
    '|<![A-Z][\\s\\S]*?(?:>[^\\n]*\\n*|$)' +
    '|<!\\[CDATA\\[[\\s\\S]*?(?:\\]\\]>[^\\n]*\\n*|$)' +
    '|</?(?:' + BLOCK_TAGS + ')(?:[ \\t]+|\\n|/?>|$)[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)' +
    '|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?:' + ATTR + ')*? */?>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)' +
    '|</[a-z][a-z0-9-]*\\s*>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$))',
  'i',
);

// Setext heading (GFM variant also rejects table delimiter lines as text).
const SETEXT_SRC =
  '^(?!BULLET|CODE|FENCES|QUOTE|HEADING|HTML|TABLE)((?:.|\\n(?!\\s*?\\n|BULLET|FENCES|QUOTE|HEADING|HR|HTML|TABLE))+?)\\n {0,3}(=+|-+)[ \\t]*(?:\\n+|$)';
function setextRe(withTable) {
  return new RegExp(
    SETEXT_SRC.replace(/BULLET/g, RE.bullet.source)
      .replace(/CODE/g, '(?: {4}| {0,3}\\t)')
      .replace(/FENCES/g, ' {0,3}(?:`{3,}|~{3,})')
      .replace(/QUOTE/g, ' {0,3}>')
      .replace(/HEADING/g, ' {0,3}#{1,6}(?:\\s|$)')
      .replace(/HR/g, HR_NC)
      .replace(/HTML/g, ' {0,3}<[^\\n>]+>\\n')
      .replace(/TABLE/g, withTable ? ' {0,3}\\|?(?:[:\\- ]*\\|)+[\\:\\- ]*\\n' : ''),
  );
}
RE.setext = setextRe(true);

// Paragraph: text lines until a blank line or a block start. The list
// interruption pattern differs at top level (only "1." bullets and bullets
// followed by space + non-space interrupt) vs inside blockquotes.
function paragraphRe(listSrc) {
  const src =
    '^([^\\n]+(?:\\n(?!HR|HEADING|LHEADING|QUOTE|FENCES|LIST|HTML|TABLE|[ \\t]+\\n)[^\\n]+)*)';
  return new RegExp(
    src
      .replace(/HR/g, HR_NC)
      .replace(/\|LHEADING/g, '')
      .replace(/HEADING/g, ' {0,3}#{1,6}(?:\\s|$)')
      .replace(/QUOTE/g, ' {0,3}>')
      .replace(/FENCES/g, ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)')
      .replace(/LIST/g, listSrc)
      .replace(/HTML/g, ` {0,3}(?:</?(?:${BLOCK_TAGS})(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`)
      .replace(/TABLE/g, RE.table ? stripCaret(RE.table.source) : ''),
  );
}
RE.paragraphTop = paragraphRe(' {0,3}(?:[*+-]|1[.)])[ \\t]+[^ \\t\\n]');
RE.paragraphQuote = paragraphRe(' {0,3}(?:[*+-]|\\d{1,9}[.)])(?:[ \\t]|\\n|$)');

// Blockquote: groups of > lines; inner paragraph pattern is the quote one.
RE.blockquote = new RegExp(
  '^( {0,3}> ?(?:(?![ \\t]*(?:\\n|$))' +
    '(?:[^\\n]+(?:\\n(?!' +
    HR_NC +
    '| {0,3}#{1,6}(?:\\s|$)| {0,3}>| {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)| {0,3}(?:[*+-]|\\d{1,9}[.)])(?:[ \\t]|\\n|$)| {0,3}(?:</?(?:' +
    BLOCK_TAGS +
    ')(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)|[ \\t]+\\n)[^\\n]+)*)' +
    '|[^\\n]*)(?:\\n|$))+',
);

// Table (GFM).
RE.table = new RegExp(
  '^ *([^\\n ].*)\\n {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)(?:\\n((?:(?! *\\n|' +
    HR_NC +
    '| {0,3}#{1,6}(?:\\s|$)| {0,3}>|(?: {4}| {0,3}\\t)[^\\n]| {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)| {0,3}(?:[*+-]|1[.)])[ \\t]| {0,3}(?:</?(?:' +
    BLOCK_TAGS +
    ')(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)).*(?:\\n|$))*)\\n*|$)',
);
// paragraphRe references RE.table; rebuild now that it exists.
RE.paragraphTop = paragraphRe(' {0,3}(?:[*+-]|1[.)])[ \\t]+[^ \\t\\n]');
RE.paragraphQuote = paragraphRe(' {0,3}(?:[*+-]|\\d{1,9}[.)])(?:[ \\t]|\\n|$)');

// ---------- inline regexes ----------
const PUNCT = '[\\p{P}\\p{S}]';
const PUNCT_NT = '(?!~)[\\p{P}\\p{S}]'; // punctuation other than ~
const PUNCT_SPACE = '[\\s\\p{P}\\p{S}]';
const PUNCT_SPACE_NT = '(?!~)[\\s\\p{P}\\p{S}]';
const NOT_PUNCT_SPACE = '[^\\s\\p{P}\\p{S}]';
const NOT_PUNCT_SPACE_T = '(?:[^\\s\\p{P}\\p{S}]|~)';

const INLINE = {
  escape: /^\\([!"#$%&'()*+,\-./:;<=>?@\[\]\\^_`{|}~])/,
  code: /^(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/,
  br: /^( {2,}|\\)\n(?!\s*$)[ \t]*/,
  autolink:
    /^<([a-zA-Z][a-zA-Z0-9+.-]{1,31}:[^\s\x00-\x1f<>]*|[a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_]))>/,
  tag: new RegExp(
    '^<!--(?:-?>|[\\s\\S]*?-->)' +
      '|^</[a-zA-Z][a-zA-Z0-9-]*\\s*>' +
      '|^<[a-zA-Z][a-zA-Z0-9-]*(?:\\s+[a-zA-Z:_][\\w.:-]*(?:\\s*=\\s*"[^"]*"|\\s*=\\s*\'[^\']*\'|\\s*=\\s*[^\\s"\'=<>`]+)?)*\\s*/?>' +
      '|^<\\?[\\s\\S]*?\\?>' +
      '|^<![a-zA-Z]+\\s[\\s\\S]*?>' +
      '|^<!\\[CDATA\\[[\\s\\S]*?\\]\\]>',
  ),
  // Left delimiter for emphasis/strong (GFM: ~ excluded from punctuation).
  emLeft: new RegExp(
    `^(?:\\*+(?:((?!\\*)(?!~)${PUNCT})|([^\\s*]))?)|^_+(?:((?!_)(?!~)${PUNCT})|([^\\s_]))?`,
    'u',
  ),
  // Right-delimiter scanners, one per delimiter char (GFM variants).
  emRightAst: new RegExp(
    `^[^_*]*?__[^_*]*?\\*[^_*]*?(?=__)|[^*]+(?=[^*])|(?!\\*)${PUNCT_NT}(\\*+)(?=[\\s]|$)|${NOT_PUNCT_SPACE_T}(\\*+)(?!\\*)(?=${PUNCT_SPACE_NT}|$)|(?!\\*)${PUNCT_SPACE_NT}(\\*+)(?=${NOT_PUNCT_SPACE_T})|[\\s](\\*+)(?!\\*)(?=${PUNCT_NT})|(?!\\*)${PUNCT_NT}(\\*+)(?!\\*)(?=${PUNCT_NT})|${NOT_PUNCT_SPACE_T}(\\*+)(?=${NOT_PUNCT_SPACE_T})`,
    'gu',
  ),
  emRightUnd: new RegExp(
    `^[^_*]*?\\*\\*[^_*]*?_[^_*]*?(?=\\*\\*)|[^_]+(?=[^_])|(?!_)${PUNCT_NT}(_+)(?=[\\s]|$)|${NOT_PUNCT_SPACE_T}(_+)(?!_)(?=${PUNCT_SPACE_NT}|$)|(?!_)${PUNCT_SPACE_NT}(_+)(?=${NOT_PUNCT_SPACE_T})|[\\s](_+)(?!_)(?=${PUNCT_NT})|(?!_)${PUNCT_NT}(_+)(?!_)(?=${PUNCT_NT})`,
    'gu',
  ),
  delLeft: new RegExp(`^(~~?)(?:((?!~)${PUNCT})|[^\\s~])`, 'u'),
  delRight: new RegExp(
    `^[^~]+(?=[^~])|(?!~)${PUNCT}(~~?)(?=[\\s]|$)|${NOT_PUNCT_SPACE}(~~?)(?!~)(?=${PUNCT_SPACE}|$)|(?!~)${PUNCT_SPACE}(~~?)(?=${NOT_PUNCT_SPACE})|[\\s](~~?)(?!~)(?=${PUNCT})|(?!~)${PUNCT}(~~?)(?!~)(?=${PUNCT})|${NOT_PUNCT_SPACE}(~~?)(?=${NOT_PUNCT_SPACE})`,
    'gu',
  ),
  punctSingle: new RegExp(`^((?![*_])${PUNCT_SPACE})`, 'u'),
  url: new RegExp(
    '^(?:mailto:[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])' +
      '|xmpp:[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])(?:\\/[A-Za-z0-9@.]+)?' +
      '|((?:[hH][tT][tT][pP][sS]?|[fF][tT][pP]):\\/\\/|www\\.)(?:[a-zA-Z0-9\\-]+\\.?)+[^\\s<]*' +
      '|[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-]))',
  ),
  backpedal: /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*'"~)]+(?!$))+/,
  // Masking helpers (emStrongMask): hide links/code/html so their
  // delimiters cannot close emphasis started outside them.
  anyPunct: /\\([\p{P}\p{S}])/gu,
  anyPunctOutsideCode:
    /(`+)(?:[^`]|[^`][\s\S]*?[^`])\1(?!`)|`+|\\([\p{P}\p{S}])/gu,
  blockSkip: new RegExp(
    '\\[(?:[^\\[\\]`]|(?<a>`+)[^`]+\\k<a>(?!`))*?\\]\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)]|\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)])*\\))*\\)' +
      '|(?<!`)(?<b>`+)[^`]+\\k<b>(?!`)' +
      '|<[^<>]*?>',
    'g',
  ),
};

// Link label bodies (balanced brackets, escapes, code spans).
const BRACKETED_SRC = '\\[(?:\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]';
const CODE_IN_LABEL = '`+(?!`)[^`]*?`+(?!`)|``+(?=\\])';
const LABEL_BODY_SRC =
  '(?:\\[(?:' + BRACKETED_SRC + '|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|' + CODE_IN_LABEL + '|[^\\[\\]\\\\`])*?';
const LABEL_BODY_LOOSE_SRC =
  '(?:[^\\[\\]\\\\`]*(?:\\[(?:' + BRACKETED_SRC + '|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|' + CODE_IN_LABEL + ')){0,999}?[^\\[\\]\\\\`]*?';
const TITLE_SRC = '"(?:\\\\[\\s\\S]|[^"\\\\])*"|\'(?:\\\\[\\s\\S]|[^\'\\\\])*\'|\\((?:\\\\[\\s\\S]|[^)\\\\])*\\)';
INLINE.link = new RegExp(
  '^!?\\[(' + LABEL_BODY_SRC + ')\\]\\([ \\t\\n]*(<(?:\\\\.|[^\\n<>\\\\])+>|[^ \\t\\n\\x00-\\x1f]+|(?=\\)))' +
    '(?:(?:[ \\t]+(?:\\n[ \\t]*)?|\\n[ \\t]*)(' + TITLE_SRC + '))?[ \\t\\n]*\\)',
);
INLINE.reflink = new RegExp('^!?\\[(' + LABEL_BODY_SRC + ')\\]\\[(' + LABEL_INNER + ')\\]');
INLINE.nolink = new RegExp('^!?\\[(' + LABEL_INNER + ')\\](?:\\[\\])?');
INLINE.reflinkSearch = new RegExp(
  '!?\\[(' + LABEL_BODY_LOOSE_SRC + ')\\]\\[((?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\]){1,999})\\]' +
    '|!?\\[((?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\]){1,999})\\](?:\\[\\])?(?!\\()',
  'g',
);

// Split a table row on unescaped pipes (marked's de()).
function splitRow(row, count) {
  const t = row.replace(/\|/g, (ch, off, str) => {
    let odd = false, p = off;
    while (--p >= 0 && str[p] === '\\') odd = !odd;
    return odd ? '|' : ' |';
  });
  const cells = t.split(' |');
  if (cells[0].trim() || cells.shift(), cells.length > 0 && !cells.at(-1)?.trim()) cells.pop();
  if (count) {
    if (cells.length > count) cells.splice(count);
    else while (cells.length < count) cells.push('');
  }
  for (let i = 0; i < cells.length; i++) cells[i] = cells[i].trim().replace(/\\\|/g, '|');
  return cells;
}

// ---------- block parser ----------
// Per-parse state (fresh for every parse() call).
let LINKS; // normalized label -> { href, title }
let ST; // { top, inLink, inRawBlock, linkEmitted, linkParenPossible }

// Cached parameterized block regexes (compiled once, keyed by indent).
const REG_CACHE = new Map();
function cached(key, make) {
  let r = REG_CACHE.get(key);
  if (!r) {
    r = make();
    REG_CACHE.set(key, r);
  }
  return r;
}
const nextBulletRe = (n) =>
  cached('nb' + n, () => new RegExp(`^ {0,${n}}(?:[*+-]|\\d{1,9}[.)])((?:[ \t][^\\n]*)?(?:\\n|$))`));
const hrRe = (n) =>
  cached('hr' + n, () => new RegExp(`^ {0,${n}}((?:-[ \t]*){3,}|(?:_[ \t]*){3,}|(?:\\*[ \t]*){3,})(?:\\n+|$)`));
const fencesBeginRe = (n) => cached('fb' + n, () => new RegExp(`^ {0,${n}}(?:\`\`\`|~~~)`));
const headingBeginRe = (n) => cached('hb' + n, () => new RegExp(`^ {0,${n}}#{1,6}(?:\\s|$)`));
const htmlBeginRe = (n) =>
  cached(
    'ht' + n,
    () =>
      new RegExp(
        `^ {0,${n}}(?:</?(?:${BLOCK_TAGS})(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`,
        'i',
      ),
  );
const blockquoteBeginRe = (n) => cached('bq' + n, () => new RegExp(`^ {0,${n}}>`));

const BLANK_LINE = /^[ \t]*$/;
const DOUBLE_BLANK = /\n[ \t]*\n[ \t]*$/;
const ANY_LINE = /\n.*\n/;
const NON_SPACE = /[^ ]/;
const LEADING_WS = /^[ \t]+/;
const SETEXT_LINE = /^ {0,3}(?:=+|-+) *$/;
const LIST_IS_TASK = /^\[[ xX]\][ \t]+\S/;
const LIST_REPLACE_TASK = /^\[[ xX]\][ \t]+/;
const LIST_TASK_CHECKBOX = /\[[ xX]\]/;
const BQ_START = /^ {0,3}>/;
const BQ_MARKER_WS = /^( {0,3}>)([ \t]+)/gm;
const BQ_SETEXT = /\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g;
const BQ_STRIP = /^ {0,3}>[ \t]?/gm;
const CODE_REMOVE_INDENT = /^(?: {0,3}\t| {1,4})/gm;
const INDENT_CODE_COMP = /^(\s+)(?:```)/;
const BEGINNING_SPACE = /^\s+/;
const TABLE_DELIM = /[:|]/;
const TABLE_ALIGN_CHARS = /^\||\| *$/g;
const TABLE_ROW_BLANK = /\n[ \t]*$/;
const ALIGN_RIGHT = /^ *-+: *$/;
const ALIGN_CENTER = /^ *:-+: *$/;
const ALIGN_LEFT = /^ *:-+ *$/;
const NOT_SPACE_START = /^\S*/;
const ENDING_NEWLINE = /\n$/;

// Fenced-code indent compensation: strip the opening fence's indent from
// each content line (up to that many leading spaces).
function dedentFence(raw, content) {
  const m = raw.match(INDENT_CODE_COMP);
  if (!m) return content;
  const pad = m[1];
  return content
    .split('\n')
    .map((line) => {
      const lead = line.match(BEGINNING_SPACE);
      if (!lead) return line;
      return line.slice(Math.min(lead[0].length, pad.length));
    })
    .join('\n');
}

function tryBlockquote(s) {
  const m = RE.blockquote.exec(s);
  if (!m) return null;
  const lines = stripTail(m[0], '\n').split('\n');
  let raw = '';
  let text = '';
  const tokens = [];
  while (lines.length > 0) {
    let seen = false;
    const group = [];
    let p;
    for (p = 0; p < lines.length; p++) {
      if (BQ_START.test(lines[p])) {
        group.push(lines[p]);
        seen = true;
      } else if (!seen) group.push(lines[p]);
      else break;
    }
    lines.splice(0, p);
    const chunk = group.join('\n');
    const stripped = chunk
      .replace(BQ_MARKER_WS, (g, b, ws) => b + expandTabs(ws, b.length))
      .replace(BQ_SETEXT, '\n    $1')
      .replace(BQ_STRIP, '');
    raw = raw ? raw + '\n' + chunk : chunk;
    text = text ? text + '\n' + stripped : stripped;
    const savedTop = ST.top;
    ST.top = true;
    blockParse(stripped, tokens, true);
    ST.top = savedTop;
    if (lines.length === 0) break;
    const last = tokens.at(-1);
    if (last?.t === 'code' || last?.t === 'heading' || last?.t === 'hr' || last?.t === 'html' || last?.t === 'table') break;
    if (last?.t === 'blockquote') {
      const rest = lines.join('\n');
      const combined = last.raw + '\n' + rest.replace(BQ_STRIP, '');
      const inner = tryBlockquote(combined);
      tokens[tokens.length - 1] = inner;
      const tail = combined.substring(inner.raw.length).replace(/^\n/, '');
      const tailLines = tail ? tail.split('\n').length : 0;
      const consumed = tailLines ? lines.slice(0, -tailLines) : lines;
      if (consumed.length > 0) raw = raw + '\n' + consumed.join('\n');
      text = text.substring(0, text.length - last.text.length) + inner.text;
      lines.splice(0, consumed.length);
      if (lines.length > 0 && BQ_START.test(lines[0])) continue;
      break;
    } else if (last?.t === 'list') {
      const combined = last.raw + '\n' + lines.join('\n');
      const inner = tryList(combined);
      tokens[tokens.length - 1] = inner;
      const extra =
        inner.raw.length > last.raw.length
          ? combined.slice(last.raw.length + 1, inner.raw.length).split('\n').length
          : 0;
      if (extra > 0) {
        const y = lines.slice(0, extra).join('\n');
        raw = raw + '\n' + y;
        text = text + '\n' + y;
      }
      lines.splice(0, extra);
      continue;
    }
  }
  return { t: 'blockquote', raw, text, items: tokens };
}

function tryList(s) {
  const first = RE.listStart.exec(s);
  if (!first) return null;
  let e = s;
  const src = s;
  const consumed = () => src.length - e.length;
  const bullet = first[1].trim();
  const ordered = bullet.length > 1;
  const list = {
    t: 'list',
    raw: '',
    ordered,
    start: ordered ? +bullet.slice(0, -1) : '',
    loose: false,
    items: [],
  };
  const bullPat = ordered ? `\\d{1,9}\\${bullet.slice(-1)}` : `\\${bullet}`;
  const itemRe = new RegExp(`^( {0,3}${bullPat})((?:[ \\t][^\\n]*)?(?:\\n|$))`);
  let pendingLoose = false;
  while (e) {
    let emptyItem = false;
    let d = '';
    let t = itemRe.exec(e);
    if (!t || RE.hr.test(e)) break;
    const startOff = consumed();
    e = e.substring(t[0].length);
    let g = t[2].split('\n', 1)[0];
    const b = t[1].length;
    let line = g.replace(LEADING_WS, (v) => expandTabs(v, b));
    const nextLine = e.split('\n', 1)[0];
    const isEmpty = !line.trim();
    let indent;
    if (isEmpty) {
      indent = b + 1;
    } else {
      indent = line.search(NON_SPACE);
      indent = indent > 4 ? 1 : indent;
      d = line.slice(indent);
      indent += b;
    }
    if (isEmpty && BLANK_LINE.test(nextLine)) {
      e = e.substring(nextLine.length + 1);
      emptyItem = true;
    }
    if (!emptyItem) {
      // The indent passed to these lookahead regexes is clamped to
      // [0, 3] as (indent - 1), so a bullet at exactly the content indent
      // does not end the item (it belongs inside it).
      const ri = Math.max(0, Math.min(3, indent - 1));
      const nb = nextBulletRe(ri);
      const hrR = hrRe(ri);
      const fb = fencesBeginRe(ri);
      const hb = headingBeginRe(ri);
      const ht = htmlBeginRe(ri);
      const bq = blockquoteBeginRe(ri);
      let blankPrev = isEmpty;
      while (e) {
        const cur = e.split('\n', 1)[0];
        const f = cur;
        const z = f.replace(LEADING_WS, (ws) => expandTabs(ws));
        if (fb.test(f) || hb.test(f) || ht.test(f) || bq.test(f) || nb.test(f) || hrR.test(f)) break;
        if (z.search(NON_SPACE) >= indent || !f.trim()) {
          d += '\n' + z.slice(indent);
        } else {
          if (
            blankPrev ||
            line.replace(/\t/g, '    ').search(NON_SPACE) >= 4 ||
            fb.test(line) ||
            hb.test(line) ||
            ht.test(line) ||
            hrR.test(line)
          )
            break;
          const qe =
            SETEXT_LINE.test(f) && RE.setext.test(line + '\n' + f)
              ? '    ' + z.replace(/^ {0,3}/, '')
              : f;
          d += '\n' + qe;
        }
        blankPrev = !f.trim();
        line = z.slice(indent);
        e = e.substring(cur.length + 1);
      }
    }
    const itemRaw = src.slice(startOff, consumed());
    if (list.loose || (pendingLoose ? (list.loose = true) : DOUBLE_BLANK.test(itemRaw) && (pendingLoose = true))) {
      // loose flag updated above
    }
    list.items.push({
      t: 'item',
      raw: itemRaw,
      task: LIST_IS_TASK.test(d),
      loose: false,
      text: d,
      blocks: [],
    });
  }
  const lastItem = list.items.at(-1);
  if (!lastItem) return null;
  lastItem.raw = lastItem.raw.trimEnd();
  lastItem.text = lastItem.text.trimEnd();
  list.raw = src.slice(0, consumed()).trimEnd();
  for (const item of list.items) {
    ST.top = false;
    item.blocks = blockParse(item.text, [], false);
    if (!list.loose) {
      const spaces = item.blocks.filter((n) => n.t === 'space');
      if (spaces.length > 0 && spaces.some((n) => ANY_LINE.test(n.raw))) list.loose = true;
    }
  }
  for (const item of list.items) {
    const head = item.blocks[0];
    if (item.task && (head?.t === 'text' || head?.t === 'paragraph')) {
      item.text = item.text.replace(LIST_REPLACE_TASK, '');
      head.raw = head.raw.replace(LIST_REPLACE_TASK, '');
      head.text = head.text.replace(LIST_REPLACE_TASK, '');
      const ck = LIST_TASK_CHECKBOX.exec(item.raw);
      if (ck) {
        const box = { t: 'checkbox', raw: ck[0] + ' ', checked: ck[0] !== '[ ]' };
        item.checked = box.checked;
        if (list.loose) {
          if (item.blocks[0] && ['paragraph', 'text'].includes(item.blocks[0].t) && 'text' in item.blocks[0]) {
            // The checkbox goes in front of the paragraph's rendered text;
            // the marker was already stripped from the text itself.
            item.blocks[0].pre = box;
          } else {
            item.blocks.unshift({ t: 'paragraph', raw: box.raw, text: '', pre: box });
          }
        } else {
          item.blocks.unshift(box);
        }
      }
    } else if (item.task) {
      item.task = false;
    }
  }
  if (list.loose) {
    for (const item of list.items) {
      item.loose = true;
      for (const n of item.blocks) if (n.t === 'text') n.t = 'paragraph';
    }
  }
  return list;
}

// Main block scanner. Appends nodes to `out` (default fresh array) and
// returns it. `mergePara` lets a leading paragraph merge into the previous
// paragraph node of `out` (blockquote chunk continuation).
function blockParse(src, out = [], mergePara = false) {
  let s = src;
  let guard = Infinity;
  while (s) {
    if (s.length < guard) guard = s.length;
    else break; // no progress: stop rather than loop forever
    let m;
    if ((m = RE.newline.exec(s))) {
      if (m[0].length === 1 && out.length) out.at(-1).raw += '\n';
      else out.push({ t: 'space', raw: m[0] });
      s = s.substring(m[0].length);
      continue;
    }
    if ((m = RE.indentedCode.exec(s))) {
      const raw = trimTrailingBlanks(m[0]);
      const text = raw.replace(CODE_REMOVE_INDENT, '');
      const node = { t: 'code', raw, text };
      const prev = out.at(-1);
      if (prev?.t === 'paragraph' || prev?.t === 'text') {
        prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + raw;
        prev.text += '\n' + text;
      } else out.push(node);
      s = s.substring(m[0].length);
      continue;
    }
    if ((m = RE.fences.exec(s))) {
      const raw = m[0];
      const lang = m[2] ? m[2].trim().replace(INLINE.anyPunct, '$1') : m[2];
      out.push({ t: 'code', raw, lang, text: dedentFence(raw, m[3] || '') });
      s = s.substring(raw.length);
      continue;
    }
    if ((m = RE.atx.exec(s))) {
      let text = m[2].trim();
      if (/#$/.test(text)) {
        const stripped = stripTail(text, '#');
        if (!stripped || /[ \t]$/.test(stripped)) text = stripped.trim();
      }
      out.push({ t: 'heading', raw: stripTail(m[0], '\n'), depth: m[1].length, text });
      s = s.substring(m[0].length);
      continue;
    }
    if ((m = RE.hr.exec(s))) {
      out.push({ t: 'hr', raw: stripTail(m[0], '\n') });
      s = s.substring(m[0].length);
      continue;
    }
    let bq;
    if ((bq = tryBlockquote(s))) {
      out.push(bq);
      s = s.substring(bq.raw.length);
      continue;
    }
    let li;
    if ((li = tryList(s))) {
      out.push(li);
      s = s.substring(li.raw.length);
      continue;
    }
    if ((m = RE.htmlBlock.exec(s))) {
      const raw = trimTrailingBlanks(m[0]);
      out.push({ t: 'html', raw, text: raw });
      s = s.substring(m[0].length);
      continue;
    }
    if ((m = RE.def.exec(s))) {
      if (!/^</.test(m[2]) && parenBalance(m[2], '()') !== -1) {
        // not a definition: fall through to paragraph/text handling
      } else {
        const tag = normLabel(m[1]);
        const href = m[2] ? m[2].replace(/^<(.*)>$/, '$1').replace(INLINE.anyPunct, '$1') : '';
        const title = m[3] ? m[3].substring(1, m[3].length - 1).replace(INLINE.anyPunct, '$1') : m[3];
        const node = { t: 'def', tag, href, title, raw: stripTail(m[0], '\n') };
        const prev = out.at(-1);
        if (prev?.t === 'paragraph' || prev?.t === 'text') {
          prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + node.raw;
          prev.text += '\n' + node.raw;
        } else {
          if (!Object.hasOwn(LINKS, tag)) LINKS[tag] = { href, title };
          out.push(node);
        }
        s = s.substring(m[0].length);
        continue;
      }
    }
    let tb;
    if ((tb = RE.table.exec(s)) && TABLE_DELIM.test(tb[2])) {
      const header = splitRow(tb[1]);
      const delim = tb[2].replace(TABLE_ALIGN_CHARS, '').split('|');
      if (header.length === delim.length) {
        const align = delim.map((c) =>
          ALIGN_RIGHT.test(c) ? 'right' : ALIGN_CENTER.test(c) ? 'center' : ALIGN_LEFT.test(c) ? 'left' : null,
        );
        const rows = tb[3]?.trim() ? tb[3].replace(TABLE_ROW_BLANK, '').split('\n') : [];
        out.push({
          t: 'table',
          raw: stripTail(tb[0], '\n'),
          header: header.map((text, i) => ({ text, align: align[i] })),
          rows: rows.map((r) => splitRow(r, header.length).map((text, i) => ({ text, align: align[i] }))),
        });
        s = s.substring(tb[0].length);
        continue;
      }
    }
    if ((m = RE.setext.exec(s))) {
      out.push({
        t: 'heading',
        raw: stripTail(m[0], '\n'),
        depth: m[2].charAt(0) === '=' ? 1 : 2,
        text: m[1].trim(),
      });
      s = s.substring(m[0].length);
      continue;
    }
    if (ST.top && (m = RE.paragraphTop.exec(s))) {
      const text = m[1].charAt(m[1].length - 1) === '\n' ? m[1].slice(0, -1) : m[1];
      const node = { t: 'paragraph', raw: m[0], text };
      const prev = out.at(-1);
      if (mergePara && prev?.t === 'paragraph') {
        prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + node.raw;
        prev.text += '\n' + node.text;
      } else out.push(node);
      mergePara = false;
      s = s.substring(m[0].length);
      continue;
    }
    if ((m = /^[^\n]+/.exec(s))) {
      const node = { t: 'text', raw: m[0], text: m[0] };
      const prev = out.at(-1);
      if (prev?.t === 'text') {
        prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + node.raw;
        prev.text += '\n' + node.text;
      } else out.push(node);
      s = s.substring(m[0].length);
      continue;
    }
    break;
  }
  ST.top = true;
  return out;
}

// ---------- inline parser ----------

// Does the text contain a link (inline or reference) — used while masking
// so nested reference links are hidden from emphasis matching.
function linkInText(s) {
  if (!s.includes('[')) return false;
  for (const m of s.matchAll(INLINE.blockSkip)) {
    if (INLINE.link.test(m[0]) && s.charAt(m.index - 1) !== '!') return true;
  }
  for (const m of s.matchAll(new RegExp(INLINE.reflinkSearch.source, 'g'))) {
    const r = m[0].lastIndexOf('[');
    if (
      !(m[0].charAt(0) === '!' || !Object.hasOwn(LINKS, normLabel(m[0].slice(r + 1, -1)))) &&
      !(r > 1 && linkInText(m[0].slice(1, r - 1)))
    )
      return true;
  }
  return false;
}

// Mask an inline source for emphasis/delimiter matching: reference links,
// inline links, code spans and raw HTML are replaced by same-length
// placeholders so delimiters inside them cannot close emphasis outside.
function maskEm(src) {
  let t = src;
  if (src.includes('[')) {
    const re = new RegExp(INLINE.reflinkSearch.source, 'g');
    const hide = (r) => {
      const o = r.lastIndexOf('[');
      if (!Object.hasOwn(LINKS, normLabel(r.slice(o + 1, -1)))) return r;
      if (o > 1 && r.charAt(0) !== '!') {
        const inner = r.slice(1, o - 1);
        if (linkInText(inner))
          return '[' + inner.replace(re, hide) + '][' + 'a'.repeat(r.length - o - 2) + ']';
      }
      return '[' + 'a'.repeat(r.length - 2) + ']';
    };
    t = t.replace(re, hide);
  }
  t = t.replace(INLINE.anyPunctOutsideCode, (n, s, r) =>
    r ? '+'.repeat(n.length) : s ? s + n.slice(s.length, -s.length).replace(/`/g, '+') + s : n,
  );
  t = t.replace(INLINE.blockSkip, (n) => '[' + 'a'.repeat(n.length - 2) + ']');
  return t;
}

// Last index in `masked` where a delimiter run of `ch` could close
// emphasis: a run whose preceding character is not blank. Also returns the
// last possible `~~` closer.
function lastClosers(masked) {
  const out = { '*': -1, _: -1, '~': -1 };
  for (let s = 0; s < masked.length; s++) {
    const r = masked[s];
    if (r !== '*' && r !== '_' && r !== '~') continue;
    const prev = s === 0 ? '\n' : masked[s - 1];
    let j = s + 1;
    while (j < masked.length && masked[j] === r) j++;
    if (prev !== ' ' && prev !== '\t' && prev !== '\n' && prev !== '\r' && prev !== '\f') out[r] = s;
    s = j - 1;
  }
  return out;
}

// Is there a raw tag/autolink starting inside the label that runs past the
// label's end? If so the bracket is not a link (marked's Be()).
function labelHasOpenTag(full, label, off) {
  if (!label.includes('<')) return false;
  for (let s = 0; s < label.length; s++) {
    if (label[s] === '\\') {
      s++;
      continue;
    }
    if (label[s] === '`') {
      const i = INLINE.code.exec(label.slice(s));
      if (i) {
        s += i[0].length - 1;
        continue;
      }
    }
    if (label[s] !== '<') continue;
    const rest = full.slice(off + s);
    const o = INLINE.tag.exec(rest) || INLINE.autolink.exec(rest);
    if (o) {
      if (o[0].length > label.length - s) return true;
      s += o[0].length - 1;
    }
  }
  return false;
}

function checkboxHtml(box) {
  return '<input ' + (box.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
}

// Build a link/image from a matched bracket pair (marked's De()).
// Returns { html, len } or null when the link must be dropped (a link was
// emitted inside its own text).
function makeLink(m, href, title, plain) {
  const label = m[1].replace(/\\([\[\]])/g, '$1');
  const isImage = m[0].charAt(0) === '!';
  const savedInLink = ST.inLink;
  const savedEmitted = ST.linkEmitted;
  const savedRaw = ST.inRawBlock;
  ST.inLink = true;
  ST.linkEmitted = false;
  const inner = inlineLoop(label, isImage ? true : plain);
  const emittedInside = ST.linkEmitted;
  ST.linkEmitted = savedEmitted;
  ST.inLink = savedInLink;
  if (!isImage) {
    if (emittedInside) {
      ST.inRawBlock = savedRaw;
      return null;
    }
    ST.linkEmitted = true;
  }
  // Plain-text rendering (image alt text): a link or image contributes
  // only its label text, no markup.
  if (plain) return { html: inner, len: m[0].length };
  if (isImage) {
    const enc = encodeHref(href);
    if (enc === null) return { html: esc(inner), len: m[0].length };
    let o = '<img src="' + esc(enc) + '" alt="' + esc(inner) + '"';
    if (title) o += ' title="' + esc(title) + '"';
    return { html: o + '>', len: m[0].length };
  }
  const enc = encodeHref(href);
  if (enc === null) return { html: inner, len: m[0].length };
  let o = '<a href="' + esc(enc) + '"';
  if (title) o += ' title="' + esc(title) + '"';
  return { html: o + '>' + inner + '</a>', len: m[0].length };
}

function tryLink(rem, plain) {
  if (!ST.linkParenPossible) return null;
  const m = INLINE.link.exec(rem);
  if (!m) return null;
  const off = m[0].charAt(0) === '!' ? 2 : 1;
  if (labelHasOpenTag(rem, m[1], off)) return null;
  let href = m[2].trim();
  if (/^</.test(href)) {
    if (!/>$/.test(href)) return null;
    const stripped = stripTail(href.slice(0, -1), '\\');
    if ((href.length - stripped.length) % 2 === 0) return null;
  } else {
    const bal = parenBalance(m[2], '()');
    if (bal === -2) return null;
    if (bal > -1) {
      const h = (m[0].indexOf('!') === 0 ? 5 : 4) + m[1].length + bal;
      m[2] = m[2].substring(0, bal);
      m[0] = m[0].substring(0, h).trim();
      m[3] = '';
    }
  }
  const tail = stripTail(m[0].slice(0, -1), '\\');
  if ((m[0].length - tail.length) % 2 === 0) return null;
  let dest = m[2];
  const title = m[3] ? m[3].slice(1, -1) : '';
  dest = dest.trim();
  if (/^</.test(dest)) dest = dest.slice(1, -1);
  return makeLink(
    m,
    dest && dest.replace(INLINE.anyPunct, '$1'),
    title && title.replace(INLINE.anyPunct, '$1'),
    plain,
  );
}

function tryReflink(rem, plain) {
  const m = INLINE.reflink.exec(rem) || INLINE.nolink.exec(rem);
  if (!m) return null;
  const off = m[0].charAt(0) === '!' ? 2 : 1;
  if (labelHasOpenTag(rem, m[1], off)) return null;
  const ref = LINKS[normLabel(m[2] || m[1])];
  if (!ref) {
    const ch = m[0].charAt(0);
    return { html: ch, len: 1, isText: true };
  }
  return makeLink(m, ref.href, ref.title, plain);
}

function tryEmStrong(rem, masked, closers, prev, plain) {
  const m = INLINE.emLeft.exec(rem);
  if (!m || (!m[1] && !m[2] && !m[3] && !m[4])) return null;
  const ch = m[0][0];
  const samePrev = prev === ch;
  const i = masked.length - rem.length;
  let l = i;
  while (l > 0 && masked[l - 1] === ch) l--;
  const before = [...masked.slice(Math.max(0, l - 2), l)].at(-1) ?? '';
  const beforePunct = before === '*' || before === '_' || INLINE.punctSingle.test(before);
  let n = prev;
  if (l < i) n = before;
  const u = l < i ? beforePunct : INLINE.punctSingle.test(n);
  if (m[4] && /[\p{L}\p{N}]/u.test(n)) return null;
  const d = m[1] || m[3] || '';
  if (!d || !n || u) {
    const k = [...m[0]].length - 1;
    let need = k;
    let f = 0;
    const y = i - l + k;
    const canAlsoClose = !!before.trim() && (!!d || (ch === '*' && !beforePunct));
    const scan = ch === '*' ? INLINE.emRightAst : INLINE.emRightUnd;
    const v = closers[ch];
    const q = masked.length - rem.length + k;
    if (v < q) return null;
    const tail = masked.slice(-rem.length + k);
    const limit = v - q;
    scan.lastIndex = 0;
    let s;
    while ((s = scan.exec(tail)) !== null && !(s.index > limit)) {
      const g = s[1] || s[2] || s[3] || s[4] || s[5] || s[6];
      if (!g) continue;
      const b = [...g].length;
      if (s[3] || s[4]) {
        need += b;
        continue;
      } else if (s[5] || s[6] || canAlsoClose) {
        if (samePrev && (s[5] || s[6])) break;
        if (y % 3 && !((y + b) % 3)) {
          f += b;
          continue;
        }
      }
      need -= b;
      if (need > 0) continue;
      const use = Math.min(b, b + need + f);
      const te = [...s[0]][0].length;
      const raw = rem.slice(0, k + s.index + te + use);
      if (Math.min(k, use) % 2) {
        const inner = raw.slice(1, -1);
        return { html: plain ? inlineLoop(inner, true) : '<em>' + inlineLoop(inner, false) + '</em>', len: raw.length };
      }
      const inner = raw.slice(2, -2);
      return { html: plain ? inlineLoop(inner, true) : '<strong>' + inlineLoop(inner, false) + '</strong>', len: raw.length };
    }
  }
  return null;
}

function tryDel(rem, masked, closers, prev, plain) {
  const m = INLINE.delLeft.exec(rem);
  if (!m) return null;
  if (!(m[1] || '') || !prev || INLINE.punctSingle.test(prev)) {
    const o = [...m[0]].length - 1;
    let p = o;
    const scan = INLINE.delRight;
    const v = closers['~'];
    const d = masked.length - rem.length + o;
    if (v < d) return null;
    const tail = masked.slice(-rem.length + o);
    const limit = v - d;
    scan.lastIndex = 0;
    let s;
    while ((s = scan.exec(tail)) !== null && !(s.index > limit)) {
      const g = s[1] || s[2] || s[3] || s[4] || s[5] || s[6];
      if (!g) continue;
      const l = [...g].length;
      if (l !== o) continue;
      if (s[3] || s[4]) {
        p += l;
        continue;
      }
      p -= l;
      if (p > 0) continue;
      const use = Math.min(l, l + p);
      const te = [...s[0]][0].length;
      const raw = rem.slice(0, o + s.index + te + use);
      const inner = raw.slice(o, -o);
      return { html: plain ? inlineLoop(inner, true) : '<del>' + inlineLoop(inner, false) + '</del>', len: raw.length };
    }
  }
  return null;
}

function tryAutolink(rem, plain) {
  const m = INLINE.autolink.exec(rem);
  if (!m) return null;
  const text = m[1];
  if (plain) return { html: text, len: m[0].length };
  const href = m[2] === '@' ? 'mailto:' + text : text;
  const enc = encodeHref(href);
  if (enc === null) return { html: esc(text, true), len: m[0].length };
  return { html: '<a href="' + esc(enc, true) + '">' + esc(text, true) + '</a>', len: m[0].length };
}

function tryUrl(rem, plain) {
  const m = INLINE.url.exec(rem);
  if (!m) return null;
  let text;
  let href;
  if (m[0].startsWith('mailto:') || m[0].startsWith('xmpp:')) {
    text = m[0];
    href = m[0];
  } else if (m[2] === '@') {
    text = m[0];
    href = 'mailto:' + m[0];
  } else {
    let cur = m[0];
    let prev;
    do {
      prev = cur;
      cur = INLINE.backpedal.exec(cur)?.[0] ?? '';
    } while (prev !== cur);
    text = cur;
    href = m[1] === 'www.' ? 'http://' + cur : cur;
  }
  if (plain) return { html: text, len: text.length };
  const enc = encodeHref(href);
  if (enc === null) return { html: esc(text, true), len: m[0].length };
  return { html: '<a href="' + esc(enc, true) + '">' + esc(text, true) + '</a>', len: text.length };
}

// Scan one plain-text run starting at `pos`. Stops before any character
// that can start an inline token, a www./protocol/email/mailto: start, or
// a hard-break run of spaces. Always consumes at least one character.
const EMAIL_LOCAL = "A-Za-z0-9.!#$%&'*+/=?^_`{|}~-";
const EMAIL_START = new RegExp(`^[${EMAIL_LOCAL}]+@`);
const PROTO_START = /^[hH][tT][tT][pP][sS]?[fF]?[tT]?[pP]?:\/\//;
function textRun(src, pos) {
  const start = pos;
  const n = src.length;
  // A text run starts with a whole run of backticks or tildes (or one
  // other character), the way marked's text token does.
  if (src[pos] === '`' || src[pos] === '~') {
    const c = src[pos];
    while (pos < n && src[pos] === c) pos++;
  }
  while (pos < n) {
    const c = src[pos];
    if (pos > start) {
      if (
        c === '\\' || c === '`' || c === '<' || c === '!' || c === '[' ||
        c === '*' || c === '_' || c === '~'
      )
        break;
      if (c === ' ' && /^ {2,}\n/.test(src.slice(pos))) break;
      if (c === 'w' && src.startsWith('www.', pos)) {
        const p = pos === 0 ? '' : src[pos - 1];
        if (pos === 0 || p === ' ' || p === '\t' || p === '\n' || p === '*' || p === '_' || p === '~' || p === '(' || p === '[') break;
      }
      if ((c === 'h' || c === 'H' || c === 'f' || c === 'F') && PROTO_START.test(src.slice(pos))) break;
      if ((c === 'm' || c === 'x') && (src.startsWith('mailto:', pos) || src.startsWith('xmpp:', pos))) {
        const p = src[pos - 1];
        if (!/[A-Za-z0-9]/.test(p)) break;
      }
      if (EMAIL_START.test(src.slice(pos))) {
        const p = src[pos - 1];
        if (!new RegExp(`^[${EMAIL_LOCAL}]$`).test(p)) break;
      }
    }
    pos++;
  }
  if (pos === start) pos++;
  return { text: src.slice(start, pos), len: pos - start };
}

// The inline loop. `plain` renders with text-renderer semantics (for image
// alt text). Recursive calls share the lexer state; only the top-level
// inline() resets inRawBlock.
function inlineLoop(src, plain) {
  const savedParen = ST.linkParenPossible;
  ST.linkParenPossible = savedParen && src.includes(')');
  try {
    return inlineBody(src, plain);
  } finally {
    ST.linkParenPossible = savedParen;
  }
}

function inlineBody(src, plain) {
  const hasDelim = src.includes('*') || src.includes('_') || src.includes('~');
  const masked = hasDelim ? maskEm(src) : src;
  let closers = null;
  const getClosers = () => (closers ?? (closers = lastClosers(masked)));
  let out = '';
  let buf = '';
  let prevChar = '';
  let pos = 0;
  // Append to the pending text run, tracking the previous character the
  // way marked does: the last character of each text run, except that a
  // run ending in '_' leaves the previous value unchanged.
  const appendText = (t) => {
    buf += t;
    const last = t.charAt(t.length - 1);
    if (last !== '_') prevChar = last;
  };
  const flush = () => {
    if (!buf) return;
    if (plain || ST.inRawBlock) out += buf;
    else out += esc(decodeRefs(buf));
    buf = '';
  };
  while (pos < src.length) {
    const rem = src.slice(pos);
    let tok = null;
    let m;
    if ((m = INLINE.escape.exec(rem))) {
      tok = { html: plain ? m[1] : esc(m[1]), len: m[0].length };
    } else if ((m = INLINE.tag.exec(rem))) {
      // The tag's state changes (<a> / <pre> etc.) apply only AFTER the
      // pending text is flushed: that text was scanned under the old state.
      let setInLink = null;
      let setInRaw = null;
      if (!ST.inLink && /^<a /i.test(m[0])) setInLink = true;
      else if (ST.inLink && /^<\/a>/i.test(m[0])) setInLink = false;
      if (!ST.inRawBlock && /^<(pre|code|kbd|script)(\s|>)/i.test(m[0])) setInRaw = true;
      else if (ST.inRawBlock && /^<\/(pre|code|kbd|script)(\s|>)/i.test(m[0])) setInRaw = false;
      tok = { html: m[0], len: m[0].length, setInLink, setInRaw };
    } else if ((tok = tryLink(rem, plain))) {
      // handled below
    } else if ((tok = tryReflink(rem, plain))) {
      // handled below
    } else if (hasDelim && (tok = tryEmStrong(rem, masked, getClosers(), prevChar, plain))) {
      // handled below
    } else if ((m = INLINE.code.exec(rem))) {
      let content = m[2].replace(/\n/g, ' ');
      if (/[^ ]/.test(content) && content.charAt(0) === ' ' && content.charAt(content.length - 1) === ' ') {
        content = content.substring(1, content.length - 1);
      }
      tok = { html: plain ? content : '<code>' + esc(content, true) + '</code>', len: m[0].length };
    } else if ((m = INLINE.br.exec(rem))) {
      tok = { html: plain ? '' : '<br>', len: m[0].length };
    } else if (hasDelim && (tok = tryDel(rem, masked, getClosers(), prevChar, plain))) {
      // handled below
    } else if ((tok = tryAutolink(rem, plain))) {
      // handled below
    } else if (!ST.inLink && (tok = tryUrl(rem, plain))) {
      // handled below
    }
    if (tok) {
      if (tok.isText) {
        appendText(tok.html);
        pos += tok.len;
        continue;
      }
      flush();
      if (tok.setInLink !== null && tok.setInLink !== undefined) ST.inLink = tok.setInLink;
      if (tok.setInRaw !== null && tok.setInRaw !== undefined) ST.inRawBlock = tok.setInRaw;
      out += tok.html;
      pos += tok.len;
      prevChar = '';
      continue;
    }
    const run = textRun(src, pos);
    appendText(run.text);
    pos += run.len;
  }
  flush();
  return out;
}

// Top-level inline render for one block's text (resets raw-block state).
function inline(src) {
  ST.inRawBlock = false;
  return inlineLoop(src, false);
}

// ---------- block renderer ----------

function renderBlocks(nodes) {
  let out = '';
  for (const n of nodes) {
    switch (n.t) {
      case 'space':
      case 'def':
        break;
      case 'code': {
        const lang = (n.lang || '').match(NOT_SPACE_START)?.[0] || '';
        const r = n.text ? n.text.replace(ENDING_NEWLINE, '') + '\n' : '';
        out += lang
          ? '<pre><code class="language-' + esc(lang) + '">' + esc(r, true) + '</code></pre>\n'
          : '<pre><code>' + esc(r, true) + '</code></pre>\n';
        break;
      }
      case 'heading':
        out += '<h' + n.depth + '>' + inline(n.text) + '</h' + n.depth + '>\n';
        break;
      case 'hr':
        out += '<hr>\n';
        break;
      case 'blockquote':
        out += '<blockquote>\n' + renderBlocks(n.items) + '</blockquote>\n';
        break;
      case 'html':
        out += n.text;
        break;
      case 'paragraph':
        out += '<p>' + (n.pre ? checkboxHtml(n.pre) : '') + inline(n.text) + '</p>\n';
        break;
      case 'text':
        out += (n.pre ? checkboxHtml(n.pre) : '') + inline(n.text);
        break;
      case 'checkbox':
        out += checkboxHtml(n);
        break;
      case 'list': {
        const tag = n.ordered ? 'ol' : 'ul';
        const start = n.ordered && n.start !== 1 ? ' start="' + n.start + '"' : '';
        let items = '';
        for (const it of n.items) items += '<li>' + renderBlocks(it.blocks) + '</li>\n';
        out += '<' + tag + start + '>\n' + items + '</' + tag + '>\n';
        break;
      }
      case 'table': {
        let head = '';
        for (const c of n.header)
          head += '<th' + (c.align ? ' align="' + c.align + '"' : '') + '>' + inline(c.text) + '</th>\n';
        let body = '';
        for (const row of n.rows) {
          let cells = '';
          for (const c of row)
            cells += '<td' + (c.align ? ' align="' + c.align + '"' : '') + '>' + inline(c.text) + '</td>\n';
          body += '<tr>\n' + cells + '</tr>\n';
        }
        out += '<table>\n<thead>\n<tr>\n' + head + '</tr>\n</thead>\n' + (body ? '<tbody>' + body + '</tbody>' : '') + '</table>\n';
        break;
      }
    }
  }
  return out;
}

// ---------- entry point ----------

export function parse(markdown) {
  const src = String(markdown).replace(/\r\n|\r/g, '\n');
  LINKS = Object.create(null);
  ST = { top: true, inLink: false, inRawBlock: false, linkEmitted: false, linkParenPossible: true };
  return renderBlocks(blockParse(src));
}
