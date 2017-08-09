noise.seed(27);

function sampleThings(avgAmount, maxAmount, v)
{
  return Math.min(maxAmount, Math.round(-Math.log(v)*avgAmount));
}


var adjectives =["afraid","ancient","angry","average","bad","big","bitter","black","blue","brave","breezy","bright","brown","calm","chatty","chilly","clever","cold","cowardly","cuddly","curly","curvy","dangerous","dry","dull","empty","evil","fast","fat","fluffy","foolish","fresh","friendly","funny","fuzzy","gentle","giant","good","great","green","grumpy","happy","hard","heavy","helpless","honest","horrible","hot","hungry","itchy","jolly","kind","lazy","light","little","loud","lovely","lucky","massive","mean","mighty","modern","moody","nasty","neat","nervous","new","nice","odd","old","orange","ordinary","perfect","pink","plastic","polite","popular","pretty","proud","purple","quick","quiet","rare","red","rotten","rude","selfish","serious","shaggy","sharp","short","shy","silent","silly","slimy","slippery","smart","smooth","soft","sour","spicy","splendid","spotty","stale","strange","strong","stupid","sweet","swift","tall","tame","tasty","tender","terrible","thin","tidy","tiny","tough","tricky","ugly","unlucky","warm","weak","wet","white","wicked","wise","witty","wonderful","yellow","young"];

var animals=["ape","baboon","badger","bat","bear","bird","bobcat","bulldog","bullfrog","cat","catfish","cheetah","chicken","chipmunk","cobra","cougar","cow","crab","deer","dingo","dodo","dog","dolphin","donkey","dragon","dragonfly","duck","eagle","earwig","eel","elephant","emu","falcon","fireant","firefox","fish","fly","fox","frog","gecko","goat","goose","grasshopper","horse","hound","husky","impala","insect","jellyfish","kangaroo","ladybug","liger","lion","lionfish","lizard","mayfly","mole","monkey","moose","moth","mouse","mule","newt","octopus","otter","owl","panda","panther","parrot","penguin","pig","puma","pug","quail","rabbit","rat","rattlesnake","robin","seahorse","sheep","shrimp","skunk","sloth","snail","snake","squid","starfish","stingray","swan","termite","tiger","treefrog","turkey","turtle","vampirebat","walrus","warthog","wasp","wolverine","wombat","yak","zebra"];
  
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

var scaleFactor = 2000.0;
  
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
  var viewRange = 7.0
  for (var x = 0; x < lookRange; x++)
  {
    var xOffset = x-Math.floor(lookRange/2);
    var curX = goodMod(latCell+xOffset, latMod);
    for (var y = 0; y < lookRange; y++)
    {
      var yOffset = y-Math.floor(lookRange/2);
      var curY = goodMod(lonCell+yOffset, lonMod);
      
      var noiseSeed = (noise.simplex2(curX, curY)+1.0)/2.0;
      var arng = new alea("" + Math.round(noiseSeed*100));
     
      
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
          
          var animal = animals[Math.floor(arng()*animals.length-0.0000001)];
          var adjective = adjectives[Math.floor(arng()*adjectives.length-0.0000001)];
          
          
          points.push([clampLatLon(actualPtX, actualPtY), adjective + " " + animal]);
        }
      }
    }
  }
  return points;
}  
