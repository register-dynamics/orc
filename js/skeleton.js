var parse = require('bennu').parse;
var text  = require('bennu').text;
var Fraction = require('fraction.js');
var base64 = require('base64-js');
var stream = require('nu-stream').stream;
var character = text.character;
var next = parse.next;
var always = parse.always;
var sequence = parse.sequence;
var enumeration = parse.enumeration;

var JSBoolean = Boolean;
var JSNumber = Number;
var JSString = String;

function logger(m='') {
  return function(v) {
    //console.log(m, v);
    /*return parse.getParserState.chain( s => {
      console.log(s);*/
      return parse.always(v);
    //})
  }
}

function complement(integer, bytes=1) {
  return ((~integer >>> 0) & (2**(bytes*8) - 1)) + 1;
}

function first(a, b) {
  return a.chain(v => next(b, always(v)));
}

function typecode(t) {
  return {type: t, primitive: null};
}

function primitive(t) {
  return {type: t.run.displayName, primitive: t}
}

var Bit7Set   = parse.token(x => /[@-_]/.test(x))
var Bit7Unset = parse.token(x => /[ -?]/.test(x))

var True  = next(character('%'), always(true));
var False = next(character('$'), always(false));

var Void  = parse.label("Void", next(character('!'), always(null)));

var Boolean = parse.label("Boolean", parse.choice(
  True,
  False
))

var HexCharacter = parse.token(x => /[0-9A-F]/.test(x))

var IntegerHexEncoding = parse.expected("pair of hex", parse.eager(parse.enumeration(
  HexCharacter.chain(logger("hex1")),
  HexCharacter.chain(logger("hex2"))
)))

var RegularMagnitudeSpecifier = parse.eager(parse.append(
  parse.manyTill(Bit7Set, Bit7Unset),
  parse.enumeration(Bit7Unset)
)).chain(values => parse.always(
  values.reduceRight((total, current, index) => total + (current.charCodeAt(0) & 0b11111) << (index * 5), 0)
))


var RegularInteger = RegularMagnitudeSpecifier.chain(logger("pairs")).chain(
  pairs => parse.eager(parse.enumerationa(new Array(pairs*2).fill(HexCharacter)))
).chain(logger("nums")).chain(
  hexLetters => parse.always(hexLetters.length > 0 ? parseInt(hexLetters.join(''), 16) : 0)
).chain(logger("final inVt"))

var ComplementMagnitudeSpecifier = parse.eager(parse.append(
  parse.manyTill(Bit7Unset, Bit7Set),
  parse.enumeration(Bit7Set)
)).chain(values => parse.always(
  values.reduceRight((total, current, index) => total + (complement(current.charCodeAt(0)) & 0b11111) << (index * 5), 0)
))

var ComplementInteger = ComplementMagnitudeSpecifier.chain(logger("c-pairs")).chain(
  pairs => parse.eager(parse.enumerationa(new Array(pairs*2).fill(HexCharacter)))
).chain(logger("c-nums")).chain(
  hexLetters => {
    var int = hexLetters.length > 0 ? parseInt(hexLetters.join(''), 16) : 0;
    var comp = complement(int, hexLetters.length/2);
    return parse.always(comp);
  }
).chain(logger("c-final int"))

// non-zero-regular-integer:
//   regular-integer
NonZeroRegularInteger = RegularInteger.chain(x =>
  x == 0 ? parse.never("Expected " + x + " to be not zero") : parse.always(x))

// non-zero-or-one-regular-integer:
//   regular-integer
NonZeroOrOneRegularInteger = RegularInteger.chain(x =>
  (x == 0 || x == 1) ? parse.never("Expected " + x + " to be not zero or one") : parse.always(x))

// non-zero-complement-integer:
//   complement-integer
NonZeroOrOneComplementInteger = ComplementInteger.chain(logger("c-non-zero-or-one")).chain(x =>
  (x == 0 || x == 1) ? parse.never("Expected " + x + " to be not zero or one") : parse.always(x))

// non-zero-or-one-complement-integer:
//   complement-integer
NonZeroComplementInteger = ComplementInteger.chain(logger("c-non-zero")).chain(x =>
  x == 0 ? parse.never("Expected " + x + " to be not zero") : parse.always(x))

// integer-list:
//   non-zero-or-one-complement-integer '~'
//   non-zero-complement-integer non-zero-or-one-regular-integer '\t'
//   non-zero-complement-integer non-zero-regular-integer integer-list
IntegerList = parse.rec(IntegerList =>
  parse.choice(
    parse.attempt(enumeration(NonZeroOrOneComplementInteger).chain(v => next(character('~'), always(v)))),
    parse.attempt(enumeration(NonZeroComplementInteger, NonZeroOrOneRegularInteger).chain(v => next(character("\t"), always(v)))),
    parse.append(enumeration(NonZeroComplementInteger, NonZeroRegularInteger), IntegerList)))

// negative-number:
//   '<' complement-integer '\t'
//   '<' complement-integer integer-list
var NegativeNumber = parse.sequence(
  character('<'),
  parse.eager(parse.cons(
    ComplementInteger.chain(v => parse.always(-v)),
    parse.choice(
      next(character("\t"), enumeration()),
      IntegerList
    )
  )
)).chain(logger("int-list 2")).chain(integers => parse.always(
  integers.reduceRight((total, current) => (total === null) ? new Fraction(current) : new Fraction(current).add(total.inverse()), null)
)).chain(logger("frac"))

// positive-number:
//   '>' regular-integer '\t'
//   '>' regular-integer integer-list
var PositiveNumber = parse.sequence(
  character('>'),
  parse.eager(parse.cons(
    RegularInteger,
    parse.choice(
      next(character("\t"), enumeration()),
      IntegerList
    )
  ).chain(logger("int-list"))
)).chain(logger("int-list 2")).chain(integers => parse.always(
  integers.reduceRight((total, current) => (total === null) ? new Fraction(current) : new Fraction(current).add(total.inverse()), null)
)).chain(logger("frac"))

// number:
//   negative-number
//   positive-number
var Number = parse.label("Number", parse.choice(
  NegativeNumber,
  PositiveNumber
))

PrintableNonTabChar = parse.token(c => !/[\u{0000}-\u{0008}\u{000A}-\u{001F}\u{007F}\u{0080}-\u{009F}\u{2028}\u{2029}\u{E0001}\u{FFF9}\u{FFFA}\u{FFFB}]/u.test(c))

// escaped-utf-8:
//   '\t' '~' escaped-utf-8
//   printable-non-tab-char escaped-utf-8
var EscapedUTF8 = parse.manyTill(
  parse.choice(
    first(character("\t"), character('~')),
    PrintableNonTabChar
  ),
  sequence(character("\t"), parse.not(character('~')))
)

// string:
//   '?' escaped-utf-8 '\t'
var String = parse.label("String", parse.eager(parse.next(
  character('?'),
  EscapedUTF8.chain(str => next(character("\t"), always(str)))
)).chain(chars =>
  parse.always(chars.join(''))
))

// base64-character:
//   char(0x41 -> 0x5A)  // [A-Z]
//   char(0x61 -> 0x7A)  // [a-z]
//   char(0x30 -> 0x39)  // [0-9]
//   '+'  // or '-' for base64url
//   '/'  // or '_' for base64url
Base64Character = parse.token(c => /[A-Za-z0-9+\/]/.test(c)).chain(logger("char"))

// base64-word:
//   base64-character base64-character base64-character base64-character
var Base64Word = parse.enumerationa(
  new Array(4).fill(Base64Character)
).chain(logger("word"))

// base64-last-word:
//   base64-character base64-character '=' '='
//   base64-character base64-character base64-character '='
//   base64-character base64-character base64-character base64-character
var Base64LastWord = parse.choice(
  parse.attempt(parse.append(parse.enumerationa(new Array(2).fill(Base64Character)), parse.enumerationa(new Array(2).fill(character('='))))),
  parse.attempt(parse.append(parse.enumerationa(new Array(3).fill(Base64Character)), parse.enumerationa(new Array(1).fill(character('='))))),
  Base64Word
).chain(logger("last word"))

// base64-words:
//   base64-last-word '\t`
//   base64-word base64-words
var Base64Words = parse.append(
  parse.manyTill(
    Base64Word,
    parse.sequence(Base64LastWord, character("\t")),
  ),
  first(parse.enumeration(Base64LastWord), character("\t"))
).chain(logger("stream of streams")).chain(s => parse.always(stream.concat(s)))

// base64:
//   '\t'
//   base64-words
var Base64 = parse.eager(parse.choice(
  next(character("\t"), enumeration()),
  Base64Words
)).chain(logger("parsing")).chain(chars => parse.always(base64.toByteArray(chars.join(''))))

// blob
//   '}' base64
var Blob = parse.label("Blob", parse.next(
  character('}'),
  Base64
))

var UserDefinedTypecode = parse.append(
  parse.manyTill(
    parse.token(x => /[`-|]/.test(x)).chain(logger('token')),
    Bit7Set
  ),
  parse.enumeration(Bit7Set)
).chain(logger("prejoin")).chain(
  chars => parse.always(typecode(stream.toArray(chars).join('')))
).chain(logger("ud-typecode"))

var Typecode = parse.label("Typecode", parse.choice(
  parse.attempt(next(character('/'), parse.late(() => PrimitiveTypecode))),
  next(character('/'), UserDefinedTypecode)
).chain(logger("typecode")))

var PrimitiveTypecode = parse.choice(
  next(character('!'), always(primitive(Void))),
  next(character('#'), always(primitive(Boolean))),
  next(character('/'), always(primitive(Typecode))),
  next(character('='), always(primitive(Number))),
  next(character('?'), always(primitive(String))),
  next(character('}'), always(primitive(Blob)))
).chain(logger("prim"))

var Primitive = parse.choice(
  Void,
  Boolean,
  Typecode,
  Number,
  String,
  Blob
)

// user-defined:
//   user-defined-typecode '\t'
//   user-defined-typecode keys '\t'
var UserDefinedType = first(
  parse.binds(
    parse.enumeration(
      UserDefinedTypecode.chain(logger("sah")),
      parse.choice(parse.late(() => Keys), enumeration()),
    ).chain(logger("udt!")),
    (udt, keys) => parse.always([udt, stream.toArray(keys)])
  ),
  character("\t")
)

// key:
//   primitive
//   user-defined-type
var Key = parse.choice(
  Primitive,
  UserDefinedType
)

// keys:
//   key
//   keys key
var Keys = parse.many1(Key)

exports = module.exports = {
  parse: x => stream.toArray(parse.run(Keys, x)),
  parseOne: x => parse.run(Key, x),
  typecode: typecode
}
