#ifdef GL_ES
precision mediump float;
#endif

uniform sampler2D state;
uniform vec2 scale;
uniform float simF;
uniform float simK;
uniform float simdA;
uniform float simdB;
uniform float simdt;

vec2 get(vec2 offset) {
    vec2 res = texture2D(state, (gl_FragCoord.xy + offset) / scale).xy;
    vec2 actualRes = vec2(res.x, res.y);
    return actualRes;
}

void main() {

  //float dA = simdA;
  float dA = 0.01;
  float dB = simdB;
  //float f = simF;
  float k = simK;
  //float dt = simdt; // not passed in rn
  
  float dt = 1.0;
  
  float largest_neighbor =
  max(get(vec2(-1.0, -1.0)).x,
  max(get(vec2(-1.0,  0.0)).x,
  max(get(vec2(-1.0,  1.0)).x,
  max(get(vec2( 0.0, -1.0)).x,
  max(get(vec2( 0.0,  1.0)).x,
  max(get(vec2( 1.0, -1.0)).x,
  max(get(vec2( 1.0,  0.0)).x,
  get(vec2( 1.0,  1.0)).x)))))));
  
  vec2 current = get(vec2(0.0, 0.0));

  float new_x = current.x;
  
  vec4 outCol = vec4(0,0,0,1.0);
  
  
  float f = 0.25;
  float FUSE_START = f;
  float FLAMMABLE_START = f*2.0;
  float FIRE_START = f*3.0;
  
  
  // Empty
  if(current.y == 0.0 || current.x < FUSE_START) {
    new_x = current.x;
  }
  // Flammable and not on fire
  else if (current.x >= FLAMMABLE_START && current.x < FIRE_START) {
    // Catch fire
    if (largest_neighbor >= FIRE_START) {
        new_x = FIRE_START+0.01;
    }
    // Don't change
  }
  // Still replenishing
  else if(current.x < FLAMMABLE_START) {
    new_x = current.x + dA;
  }
  // On fire
  else if (current.x >= FIRE_START) {
    new_x = current.x + 0.04;
    // burned out
    if (new_x >= 1.0) {
        new_x = FUSE_START+0.01;
    }
  }
  
  // empty
  if (new_x < FUSE_START || current.y == 0.0) {
    outCol = vec4(0, 0.0, 0.0, 1.0);
  }
  // fuse burned out
  if (new_x < FLAMMABLE_START) {
    outCol = vec4(new_x, current.y, new_x, 1.0);
  }
  // fuse ready
  else if(new_x < FIRE_START) {
    outCol = vec4(new_x, current.y, new_x, 1.0);
  }
  // fire
  else {
    outCol = vec4(new_x, current.y, 0.0, 1.0);
  }
  
  gl_FragColor = outCol;
}
