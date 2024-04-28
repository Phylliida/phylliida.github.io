/**
 * Game of Life simulation and display.
 * @param {HTMLCanvasElement} canvas Render target
 * @param {number} [scale] Size of each cell in pixels (power of 2)
 */
function GOL(canvas, scale) {
    var igloo = this.igloo = new Igloo(canvas);
    var gl = igloo.gl;
    if (gl == null) {
        alert('Could not initialize WebGL!');
        throw new Error('No WebGL');
    }
    scale = this.scale = scale || 8;
    var w = canvas.width, h = canvas.height;
    this.viewsize = new Float32Array([w, h]);
    this.statesize = new Float32Array([w / scale, h / scale]);
    this.timer = null;
    this.lasttick = GOL.now();
    this.fps = 0;

    gl.disable(gl.DEPTH_TEST);
    this.programs = {
        copy: igloo.program('glsl/quad.vert', 'glsl/copy.frag'),
        gol:  igloo.program('glsl/quad.vert', 'glsl/fire.frag')
    };
    this.buffers = {
        quad: igloo.array(Igloo.QUAD2)
    };
    this.textures = {
        front: igloo.texture(null, gl.RGBA, gl.REPEAT, gl.NEAREST)
            .blank(this.statesize[0], this.statesize[1]),
        back: igloo.texture(null, gl.RGBA, gl.REPEAT, gl.NEAREST)
            .blank(this.statesize[0], this.statesize[1])
    };
    this.framebuffers = {
        step: igloo.framebuffer()
    };
    this.setEmpty();
}

/**
 * @returns {number} The epoch in integer seconds
 */
GOL.now = function() {
    return Math.floor(Date.now() / 1000);
};

/**
 * Compact a simulation state into a bit array.
 * @param {Object} state Array-like state object
 * @returns {ArrayBuffer} Compacted bit array
 */
GOL.compact = function(state) {
    var compact = new Uint8Array(state.length / 8);
    for (var i = 0; i < state.length; i++) {
        var ii = Math.floor(i / 8),
            shift = i % 8,
            bit = state[i] ? 1 : 0;
        compact[ii] |= bit << shift;
    }
    return compact.buffer;
};

/**
 * Expand a simulation state from a bit array.
 * @param {ArrayBuffer} compact Compacted bit array
 * @returns {Object} Array-like state object
 */
GOL.expand = function(buffer) {
    var compact = new Uint8Array(buffer),
        state = new Uint8Array(compact.length * 8);
    for (var i = 0; i < state.length; i++) {
        var ii = Math.floor(i / 8),
            shift = i % 8;
        state[i] = (compact[ii] >> shift) & 1;
    }
    return state;
};

/**
 * Set the entire simulation state at once.
 * @param {Object} state Boolean array-like
 * @returns {GOL} this
 */
GOL.prototype.set = function(state) {
    var gl = this.igloo.gl;
    var rgba = new Uint8Array(this.statesize[0] * this.statesize[1] * 4);
    for (var i = 0; i < state.length; i++) {
        rgba[i] = state[i];
        
        /*
        var ii = i * 4;
        //rgba[ii + 0] = rgba[ii + 1] = rgba[ii + 2] = state[i] ? 255 : 0;
        rgba[ii + 2] = state[i] ? 255 : 0;
        rgba[ii + 0] = state[i] ? 0 : 255;
        rgba[ii + 1] =  state[i] ? 0 : Math.round(255/1.5);
        rgba[ii + 3] = 255;
        */
    }
    this.textures.front.subset(rgba, 0, 0, this.statesize[0], this.statesize[1]);
    return this;
};

/**
 * Fill the entire state with random values.
 * @param {number} [p] Chance of a cell being alive (0.0 to 1.0)
 * @returns {GOL} this
 */
GOL.prototype.setRandom = function(p) {
    var gl = this.igloo.gl, size = this.statesize[0] * this.statesize[1]*4;
    p = p == null ? 0.8 : p;
    var rand = new Uint8Array(size);
    for (var i = 0; i < size; i+= 4) {
        var isA = Math.random() < p;
        
        rand[i*4] = isA ? 255 : 0;
        rand[i*4+1] = 170;
        rand[i*4+2] = isA ? 0 : 255;
        rand[i*4+3] = 255;
    }
    this.set(rand);
    return this;
};

/**
 * Clear the simulation state to empty.
 * @returns {GOL} this
 */
GOL.prototype.setEmpty = function() {
  
    var emptyState = new Uint8Array(this.statesize[0] * this.statesize[1]*4);
    var numCells = this.statesize[0]*this.statesize[1];
    var ii = 0;
    for (var i = 0; i < numCells; i++)
    {
      emptyState[ii] = 0;
      emptyState[ii+1] = 0;
      emptyState[ii+2] = 0;
      emptyState[ii+3] = 255;
      ii += 4;
    }
    this.set(emptyState);
    
    
    
    return this;
};

/**
 * Swap the texture buffers.
 * @returns {GOL} this
 */
GOL.prototype.swap = function() {
    var tmp = this.textures.front;
    this.textures.front = this.textures.back;
    this.textures.back = tmp;
    return this;
};

/**
 * Step the Game of Life state on the GPU without rendering anything.
 * @returns {GOL} this
 */
GOL.prototype.step = function() {
    if (GOL.now() != this.lasttick) {
        $('.fps').text(this.fps + ' FPS');
        this.lasttick = GOL.now();
        this.fps = 0;
    } else {
        this.fps++;
    }
    var gl = this.igloo.gl;
    this.framebuffers.step.attach(this.textures.back);
    this.textures.front.bind(0);
    gl.viewport(0, 0, this.statesize[0], this.statesize[1]);
    this.programs.gol.use()
        .attrib('quad', this.buffers.quad, 2)
        .uniformi('state', 0)
        .uniform('scale', this.statesize)
        .uniform('simF', globalFVal)
        .uniform('simK', globalKVal)
        .uniform('simdA', 0.1)
        .uniform('simdB', globaldBVal)
        .draw(gl.TRIANGLE_STRIP, 4);
    this.swap();
    return this;
};

var uriHolderThing;


/**
 * Render the Game of Life state stored on the GPU.
 * @returns {GOL} this
 */
GOL.prototype.draw = function() {
    var gl = this.igloo.gl;
    this.igloo.defaultFramebuffer.bind();
    this.textures.front.bind(0);
    gl.viewport(0, 0, this.viewsize[0], this.viewsize[1]);
    this.programs.copy.use()
        .attrib('quad', this.buffers.quad, 2)
        .uniformi('state', 0)
        .uniform('scale', this.viewsize)
        .draw(gl.TRIANGLE_STRIP, 4);
    return this;
};




/**
 * Set the state at a specific position.
 * @param {number} x
 * @param {number} y
 * @param {boolean} state True/false for live/dead
 * @returns {GOL} this
 */
GOL.prototype.poke = function(x, y, state, shiftDown) {
    var gl = this.igloo.gl;
    
    if (state) {
        if (shiftDown) {
            this.textures.front.subset([0, 0, 0, 255], x, y, 1, 1);
        }
        else{ 
            this.textures.front.subset([255*0.51, 255*0.51, 255*0.51, 255], x, y, 1, 1);
        }
    }
    else {
        var gl = this.igloo.gl, w = this.statesize[0], h = this.statesize[1];
        this.framebuffers.step.attach(this.textures.front);
        var rgba = new Uint8Array(4);
        gl.readPixels(x, y, 1, 1, gl.RGBA, gl.UNSIGNED_BYTE, rgba);
        if (rgba[1] > 0 && rgba[1] > 255*0.50)
        {
            this.textures.front.subset([255*0.76, 0.51*255, 0.0, 255], x, y, 1, 1);
        }
    }
    
    
    
    return this;
};

/**
 * @returns {Object} Boolean array-like of the simulation state
 */
GOL.prototype.get = function() {
    var gl = this.igloo.gl, w = this.statesize[0], h = this.statesize[1];
    this.framebuffers.step.attach(this.textures.front);
    var rgba = new Uint8Array(w * h * 4);
    gl.readPixels(0, 0, w, h, gl.RGBA, gl.UNSIGNED_BYTE, rgba);
    var state = new Uint8Array(w * h*4);
    for (var i = 0; i < w * h*4; i++) {
        state[i] = rgba[i];
    }
    return state;
};

/**
 * Run the simulation automatically on a timer.
 * @returns {GOL} this
 */
 

 
function stepStuff()
{
  gol.step();
  gol.draw();
  setTimeout(stepStuff, 1);
}
 
GOL.prototype.start = function() {
    if (this.timer == null) {
        this.timer = setInterval(function(){
        }, 1000);
        setTimeout(stepStuff, 1000);
    }
    return this;
};


/**
 * Stop animating the simulation.
 * @returns {GOL} this
 */
GOL.prototype.stop = function() {
    clearInterval(this.timer);
    this.timer = null;
    return this;
};

/**
 * Toggle the animation state.
 * @returns {GOL} this
 */
GOL.prototype.toggle = function() {
    if (this.timer == null) {
        this.start();
    } else {
        this.stop();
    }
};

/**
 * Find simulation coordinates for event.
 * This is a workaround for Firefox bug #69787 and jQuery bug #8523.
 * @returns {Array} target-relative offset
 */
GOL.prototype.eventCoord = function(event) {
    var $target = $(event.target),
        offset = $target.offset(),
        border = 1,
        x = event.pageX - offset.left - border,
        y = $target.height() - (event.pageY - offset.top - border);
    return [Math.floor(x / this.scale), Math.floor(y / this.scale)];
};

/**
 * Manages the user interface for a simulation.
 */
function Controller(gol) {
    this.gol = gol;
    var _this = this,
        $canvas = $(gol.igloo.canvas);
    this.drag = null;
    $canvas.on('mousedown', function(event) {
        _this.drag = event.which;
        var pos = gol.eventCoord(event);
        prev_pos = pos;
        gol.poke(pos[0], pos[1], _this.drag == 1);
        gol.draw();
    });
    $canvas.on('mouseup', function(event) {
        _this.drag = null;
        prev_pos = null;
    });
    var prev_pos = null;
    $canvas.on('mousemove', function(event) {
        if (_this.drag) {
            var pos = gol.eventCoord(event);
            var x0 = pos[0];
            var y0 = pos[1];
            var x1 = prev_pos[0];
            var y1 = prev_pos[1];
            //console.log("" + min_x + "" + min_y + "" + max_x + "" + max_y);
            // Bresenham's line algorithm from wiki
            
            function plotLineLow(x0, y0, x1, y1){
                var dx = x1 - x0;
                var dy = y1 - y0;
                var yi = 1;
                if (dy < 0) {
                    yi = -1;
                    dy = -dy;
                }
                var D = (2 * dy) - dx;
                var y = y0;
                for (var x = x0; x <= x1; x++){
                    
                    gol.poke(x, y, _this.drag == 1, _this.shiftKey);
                    if (D > 0)
                    {
                        y = y + yi;
                        D = D + (2 * (dy - dx));
                    }
                    else
                    {
                        D = D + 2*dy;
                    }
                }
            }
            function plotLineHigh(x0, y0, x1, y1)
            {
                var dx = x1 - x0;
                var dy = y1 - y0;
                var xi = 1;
                if (dx < 0) {
                    xi = -1;
                    dx = -dx;
                }
                var D = (2 * dx) - dy;
                var x = x0;

                for (var y = y0; y <= y1; y++)
                {
                    gol.poke(x, y, _this.drag == 1, _this.shiftKey);
                    if (D > 0)
                    {
                        x = x + xi;
                        D = D + (2 * (dx - dy));
                    }
                    else
                    {
                        D = D + 2*dx;
                    }
                }
            }            
            
            if (Math.abs(y1 - y0) < Math.abs(x1 - x0)) {
                if (x0 > x1)
                    plotLineLow(x1, y1, x0, y0);
                else
                    plotLineLow(x0, y0, x1, y1);
            }
            else
            {
                if (y0 > y1)
                    plotLineHigh(x1, y1, x0, y0);
                else
                    plotLineHigh(x0, y0, x1, y1);
            }
            gol.draw();
            prev_pos = pos;
        }
    });
    $canvas.on('contextmenu', function(event) {
        event.preventDefault();
        return false;
    });
    $(document).on('keyup', function(event) {
        switch (event.which) {
        case 82: /* r */
            gol.setRandom();
            gol.draw();
            break;
        case 46: /* [delete] */
            gol.setEmpty();
            gol.draw();
            break;
        case 32: /* [space] */
            gol.toggle();
            break;
        case 83: /* s */
            if (event.shiftKey) {
                if (this._save) gol.set(this._save);
            } else {
                this._save = gol.get();
            }
            break;
        };
    });
}

/* Initialize everything. */
var gol = null, controller = null;
$(document).ready(function() {
    resetParams();
    //var uriHolderThingTmp = new URI();
    //uriHolderThing = new URI("https://yams.com/?" + uriHolderThingTmp.fragment());
    var $canvas = $('#life');
    gol = new GOL($canvas[0], 8).draw().start();
    controller = new Controller(gol);
});

/* Don't scroll on spacebar. */
$(window).on('keydown', function(event) {
    return !(event.keyCode === 32);
});



function assignUriToState()
{
    return;
  // get key-val dictionary of uri params
  var uriVals = uriHolderThing.search(true);
  if (uriVals.hasOwnProperty("F") && !isNaN(parseFloat(uriVals['F'])))
  {
    document.getElementById("fVal").value = Math.round(parseFloat(uriVals['F'])*1000);
    globalFVal = parseFloat(uriVals['F']);
  }
  
  if (uriVals.hasOwnProperty("K") && !isNaN(parseFloat(uriVals['K'])))
  {
    document.getElementById("kVal").value = Math.round(parseFloat(uriVals['K'])*1000);
    globalKVal = parseFloat(uriVals['K']);
  }
    
  if (uriVals.hasOwnProperty("DB") && !isNaN(parseFloat(uriVals['DB'])))
  {
    document.getElementById("dBVal").value = Math.round(parseFloat(uriVals['DB'])*1000);
    globaldBVal = parseFloat(uriVals['DB']);
  }
  
  
  //updateSliderLogs();
  
}


var globalFVal = 0.048;
var globalKVal = 0.067;
var globaldBVal = 0.286;


function modifiedSliders()
{
    return;
   if (uriHolderThing)
   {
    globalFVal = parseFloat(document.getElementById("fVal").value)/1000.0;
      globalKVal = parseFloat(document.getElementById("kVal").value)/1000.0;
    globaldBVal = parseFloat(document.getElementById("dBVal").value)/1000.0;
    uriHolderThing.search({'K': globalKVal, 'F': globalFVal, 'DB': globaldBVal});
    console.log(uriHolderThing.search() + "");
    window.location.hash = "" + uriHolderThing.query();
  }
  updateSliderLogs();

}

function updateSliderLogs() {
  //document.getElementById("curFVal").innerText = "" + globalFVal;
  //document.getElementById("curKVal").innerText = "" + globalKVal;
  //..document.getElementById("curdBVal").innerText = "" + globaldBVal;
}


function updateTextInput(val) {
          document.getElementById('textInput').value=val; 
        }

function resetParams()
{
  // 0.048 simK 0.1 simdA 1 simdB 0.286 simdt 1 is also cool
  //document.getElementById("fVal").value = 48;
  //document.getElementById("kVal").value = 67;
  //document.getElementById("dAVal").value = 1000;
  //modifiedSliders();
}


function resetSimulation()
{
  gol.setEmpty();
}
