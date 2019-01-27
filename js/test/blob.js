var skeleton = require('../skeleton');
var assert = require('assert');
var base64 = require('base64-js');
var inspect = require('util').inspect;

VECTORS = [
  ["}aGVsbG8=\t", Uint8Array.from(Array.from("hello").map(c => c.charCodeAt(0)))],
  ["}\t",         new Uint8Array(0)],
]

INVALID = [
  "}____\t",
  "}abcde\t"
]

describe("Decoding blobs", () => {
  VECTORS.forEach(vector => {
    var input = vector[0];
    var expected = vector[1];
    it("correctly decodes " + inspect(input), () => {
      var result = skeleton.parseOne(input);
      assert.deepEqual(expected, result);
    })
  })

  INVALID.forEach(input => {
    it("rejects " + inspect(input), () => {
      assert.throws(() => skeleton.parseOne(input));
    })
  })
})
