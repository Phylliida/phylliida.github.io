noise.seed(27);

function sampleThings(avgAmount, maxAmount, v)
{
  return Math.min(maxAmount, Math.round(-Math.log(v)*avgAmount));
}

  
function clampLatLon(lat, lon)
{
  var didChange = true;
  while (didChange)
  {
    didChange = false;
    while (lat > 360)
    {
      lat -= 360;
      didChange = true;
    }
    while (lat < -360)
    {
      lat += 360;
      didChange = true;
    }
    while (lon > 360)
    {
      lon -= 360;
      didChange = true;
    }
    while (lon < -360)
    {
      lon += 360;
      didChange = true;
    }
    while (lat > 90)
    {
      lat = 180-lat;
      didChange = true;
    }
    while (lat < -90)
    {
      lat = -(180+lat);
      didChange = true;
    }
    while (lon > 180)
    {
      lon -= 360;
      didChange = true;
    }
    while (lon < -180)
    {
      lon += 360;
      didChange = true;
    }
  }
  return [lat, lon]
}   
  
// Works for negative values
function goodMod(a, b)
{
  return (b + (a%b)) % b;
}
  
var latMod = 501;
var lonMod = 553;

var scaleFactor = 20000.0;
  
function generatePoints(lat, lon, seed)
{
  noise.seed(seed);
  res = clampLatLon(lat, lon);
  lat = res[0]
  lon = res[1]
  
  // lat is from -90 to 90
  lat = lat + 90.0;
  // lon is from -180 to 180
  lon = lon + 180.0;
  
  // split into about 15m wide cells
  var latCellOriginal = Math.round(lat*scaleFactor);
  var lonCellOriginal = Math.round(lon*scaleFactor);
  
  var cellActualLat = latCellOriginal/scaleFactor;
  var cellActualLon = lonCellOriginal/scaleFactor;
  
  
  var latCell = goodMod(latCellOriginal,latMod);
  var lonCell = goodMod(lonCellOriginal,lonMod);
  var points = [];
  var lookRange = 7; // this needs to be odd
  var viewRange = 4.0
  for (var x = 0; x < lookRange; x++)
  {
    var xOffset = x-Math.floor(lookRange/2);
    var curX = goodMod(latCell+xOffset, latMod);
    for (var y = 0; y < lookRange; y++)
    {
      var yOffset = y-Math.floor(lookRange/2);
      var curY = goodMod(lonCell+yOffset, lonMod);
      
      var noiseSeed = (noise.simplex2(curX, curY)+1.0)/2.0;
      var arng = new alea("" + Math.round(noiseSeed));
     
      
      var ptCountNoise = arng();
      
      var ptCount = sampleThings(3, 18, ptCountNoise);
      
      
      var curCellActualLat = cellActualLat;
      var curCellActualLon = cellActualLon;
      
      for (var i = 0; i < ptCount; i++)
      {
        var ptX = arng();
        var ptY = arng();
        if (Math.sqrt((ptX+xOffset)*(ptX+xOffset)+(ptY+yOffset)*(ptY+yOffset)) < viewRange)
        {
          var actualPtX = (latCellOriginal+xOffset+ptX)/scaleFactor-90.0;
          var actualPtY = (lonCellOriginal+yOffset+ptY)/scaleFactor-180.0;
          
          points.push(clampLatLon(actualPtX, actualPtY));
        }
      }
    }
  }
  return points;
}  
  

 
  
    
