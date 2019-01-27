var skeleton = require('../skeleton');
var Fraction = require('fraction.js');
var assert = require('assert');
var base64 = require('base64-js');
var inspect = require('util').inspect;

// https://twitter.com/databasescaling/status/1081688592378929152
TWEET = "!$%/useR}\t}Zm9vYmFy\t?Hello\t~World!\t>!01_EC\"0100\t>!01_FD!02^FEFF~<_FF_FF!04_FA~recorD?Hi\tlanG?GB-en\t\t\t"

EXPECTED = [
  null,
  false,
  true,
  skeleton.typecode("useR"),
  Uint8Array.of(),
  Uint8Array.of(0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72),
  "Hello\tWorld!",
  new Fraction(5377, 5121),
  new Fraction(2317, 1802),
  new Fraction(-6, 31),
  [skeleton.typecode("recorD"), ["Hi", [skeleton.typecode("lanG"), ["GB-en"]]]]
]

describe("Decoding Andy's tweet", () => {
  it("correctly decodes many keys of different types", () => {
    var result = skeleton.parse(TWEET);
    assert.deepStrictEqual(result, EXPECTED);
  })
})
