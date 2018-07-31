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
    vec2 res = texture2D(state, (gl_FragCoord.xy + offset) / scale).xz;
    vec2 actualRes = vec2(min(1.0, res.x*2.0), res.y);
    return actualRes;
}

void main() {

  float dA = simdA;
  float dB = simdB;
  float f = simF;
  float k = simK;
  float dt = 1.0;
  
  vec2 grad =
  get(vec2(-1.0, -1.0))*0.05 +
  get(vec2(-1.0,  0.0))*0.2 +
  get(vec2(-1.0,  1.0))*0.05 +
  get(vec2( 0.0, -1.0))*0.2 +
  get(vec2( 0.0,  0.0))*(-1.0) +
  get(vec2( 0.0,  1.0))*0.2 +
  get(vec2( 1.0, -1.0))*0.05 +
  get(vec2( 1.0,  0.0))*0.2 +
  get(vec2( 1.0,  1.0))*0.05;
  
  vec2 current = get(vec2(0.0, 0.0));
  float A = current.x;
  float B = current.y;
  float newA = A + (dA*grad.x-A*B*B + f*(1.0-A))*dt;
  float newB = B + (dB*grad.y+A*B*B - (k+f)*B)*dt;
  
  
  
  gl_FragColor = vec4(newA/2.0, newA/1.5, newB, 1.0);
}
