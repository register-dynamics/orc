var skeleton = require('../skeleton');
var assert = require('assert');
var inspect = require('util').inspect;

VECTORS = [
  ["?simon\t", "simon"],
  ["?simo\t~n\t", "simo\tn"],
  ["?i 💕 you\t", "i 💕 you"]
]

INVALID = [
  "?some tags \u007F \t"
]

describe("Decoding strings", () => {
  VECTORS.forEach(vector => {
    var input = vector[0];
    var expected = vector[1];
    it("correctly decodes " + inspect(input), () => {
      var result = skeleton.parseOne(input);
      assert.strictEqual(expected, result, "Got " + inspect(result) + ", expected " + inspect(expected));
    })
  })

  INVALID.forEach(input => {
    it("rejects " + inspect(input), () => {
      assert.throws(() => skeleton.parseOne(input));
    })
  })
})
