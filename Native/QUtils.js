Elm.Native.QUtils = {};
Elm.Native.QUtils.make = function(elm) {
  elm.Native = elm.Native || {};
  elm.Native.QUtils = elm.Native.QUtils || {};

  if (elm.Native.QUtils.values) {
    return elm.Native.QUtils.values;
  }

  function floatMod(x, y) {
    return x % y;
  }
  
  return elm.Native.QUtils.values = {
    floatMod : F2(floatMod)
  };
};
