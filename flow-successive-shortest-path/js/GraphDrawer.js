/**
 * Die Farben, die im Projekt genutzt werden.
 * Aus dem TUM Styleguide.
 * @type Object
 */
var const_Colors = {NodeFilling:            "#98C6EA",  // Pantone 283, 100%
                    NodeBorder:             "#0065BD",  // Pantone 300, 100%, "TUM-Blau"
                    NodeBorderHighlight:    "#C4071B",  // Helles Rot 100% aus TUM Styleguide
                    NodeFillingHighlight:   "#73B78D",  // Dunkelgrün 55 % aus TUM Styleguide
                    NodeFillingLight:       "#00c532",  // Dunkelgrün 55 % aus TUM Styleguide
                    NodeFillingQuestion:    "#C4071B",  // Helles Rot 100% aus TUM Styleguide
                    EdgeHighlight1:         "#C4071B",  // Helles Rot 100% aus TUM Styleguide
                    EdgeHighlight2:         "#73B78D",  // Dunkelgrün 55 % aus TUM Styleguide
                    EdgeHighlight3:         "#73B78D",  // Dunkelgrün 55 % aus TUM Styleguide
                    EdgeHighlight4:         "#007C30",  // Dunkelgrün 100 % aus TUM Styleguide
                    RedText:                "#C4071B",  // Helles Rot 100% aus TUM Styleguide
                    GreenText:              "#007C30",   // Dunkelgrün 100 % aus TUM Styleguide
    PQColor : "#FFFF70", // Helles Gelb
    StartNodeColor : "#33CC33", // Dunklgrün
    CurrentNodeColor : "#C4071B", // Helles Rot
    FinishedNodeColor : "#73B78D", // Wie EdgeHighlight2
    ShortestPathColor : "#73B78D", // Wie EdgeHighlight2
    UnusedEdgeColor : "#0065BD", // Wie NodeBorder
    NormalEdgeColor : "#000000" // Schwarz
                    };

/**
 * Standardgröße eines Knotens
 * @type Number
 */
var global_KnotenRadius = 15;                           // Radius der Knoten
/**
 * Standardaussehen einer Kante.
 * @type Object
 */
var global_Edgelayout = {'arrowAngle' : Math.PI/8,	         // Winkel des Pfeilkopfs relativ zum Pfeilkörper
			             'arrowHeadLength' : 15,             // Länge des Pfeilkopfs
                         'lineColor' : "black",		         // Farbe des Pfeils
			             'lineWidth' : 2,		             // Dicke des Pfeils
                         'font'	: 'Arial',		             // Schrifart
                         'fontSize' : 14,		             // Schriftgrösse in Pixeln
                         'isHighlighted': false,             // Ob die Kante eine besondere Markierung haben soll
                         'progressArrow': false,             // Zusätzlicher Animationspfeil
                         'progressArrowPosition': 0.0,       // Position des Animationspfeils
                         'progressArrowSource': null,        // Animationspfeil Source Knoten
                         'progressArrowTarget': null         // Animationspfeil Target Knoten
			};

/**
 * Standardaussehen eines Knotens.
 * @type Object
 */
var global_NodeLayout = {'fillStyle' : const_Colors.NodeFilling,    // Farbe der Füllung
                         'nodeRadius' : 15,                         // Radius der Kreises
                         'borderColor' : const_Colors.NodeBorder,   // Farbe des Rands (ohne Markierung)
                         'borderWidth' : 2,                         // Breite des Rands
                         'fontColor' : 'black',                     // Farbe der Schrift
                         'font' : 'bold',                           // Schriftart
                         'fontSize' : 14                            // Schriftgrösse in Pixeln
                        };

function translate(x,y){
    return "translate("+x+","+y+")";
}

GraphAlgos = d3.map();

GraphDrawer = function(svgOrigin,extraMargin,transTime){

    /////////////////
    //PRIVATE
    var id = svgOrigin.attr("id");
    GraphAlgos.set(id,this);

    var transTime = (transTime!=null) ? transTime : 250;

    var extraMargin = extraMargin || {};

    var xRange = +svgOrigin.attr("width") || 400;
        yRange = +svgOrigin.attr("height") || 300;
    var wS = global_NodeLayout['borderWidth'] +10; // had to add 10 to fit the neq node resources into frame

    var margin = {
            top: global_KnotenRadius+wS+ (extraMargin.top || 10),
            right: global_KnotenRadius+wS,
            bottom: global_KnotenRadius+wS,
            left: global_KnotenRadius+wS +(extraMargin.left || 0)}

        width = xRange - margin.left - margin.right,
        height = yRange - margin.top - margin.bottom;

    this.height = height;
    this.width = width;

    this.margin = margin;

    var radius = global_KnotenRadius;//20;

    svgOrigin
        .attr({version: '1.1' , xmlns:"http://www.w3.org/2000/svg"})
        .attr("width", width + margin.left + margin.right)
        .attr("height", height + margin.top + margin.bottom)

//     //d3.select("body").selectAll("svg")
    svgOrigin
        .append("defs").append("marker")
        .attr("id", "arrowhead2")
        .attr("refX",12) /*must be smarter way to calculate shift*/
        .attr("refY",2)
        .attr("markerWidth", 12)
        .attr("markerHeight", 4)
        .attr("orient", "auto")
        .append("path")
        .attr("d", "M 0,0 V 4 L6,2 Z"); //this is actual shape for arrowhead

    var svg = svgOrigin.append("g")
        .attr("transform", "translate(" + margin.left + "," + margin.top + ")");

    this.svg=svg;

    var svg_links=svg.append("g").attr("id", "edges");
    var svg_nodes=svg.append("g").attr("id", "nodes");

    this.x = d3.scale.linear()
        .range([margin.left, width-margin.right])
        .domain([0,xRange]);

    this.y = d3.scale.linear()
        .range([height-margin.top, margin.bottom])
        .domain([0,yRange]);

    var transform = function(d){
        return translate(this.x(this.nodeX(d)),this.y(this.nodeY(d)));
    }
    transform = transform.bind(this);

    this.squeeze = function(){
        var nodes;
        if(Graph.instance && (nodes = Graph.instance.getNodes())){
            this.x.domain(d3.extent(nodes, function(d) { return d.x; }));
            this.y.domain(d3.extent(nodes, function(d) { return d.y; }));
        }
    }

    //somehow we get old copies of nodes in d where the state is outdated
    //-> workaround: get the correct node from the Graph instance using its id
    var xfun = function(d){
        return this.x(this.nodeX(Graph.instance.nodes.get(d.id) || d));
    }

    var yfun = function(d){
        return this.y(this.nodeY(Graph.instance.nodes.get(d.id) || d));
    }

    xfun = xfun.bind(this);

    yfun = yfun.bind(this);

    function lineAttribs(d,a,b){
        var attr = { x1:xfun(d.start), y1:yfun(d.start), x2:xfun(d.end), y2:yfun(d.end)};
        if(transTime) d3.select(this).transition().duration(transTime).attr(attr)
        else d3.select(this).attr(attr);
    };

	function nodeAttribs(d,a,b){
        var attr = { x : (xfun(d.start)+xfun(d.end))*0.5 , y : ( yfun(d.start)+yfun(d.end))*.5};
        if(transTime) d3.select(this).transition().duration(transTime).attr(attr)
        else d3.select(this).attr(attr);
    };
	
	
    var text_normal_margin = 0;

    function textAttribs(d){
        var dx = xfun(d.end) - xfun(d.start);
        var dy = yfun(d.end) - yfun(d.start);
        var len = Math.sqrt(dx*dx+dy*dy);

        //rotate counterclockwise
        var normal_x = -dy / len;
        var normal_y = dx / len;

        var projected_corner_1 = this.getBBox().width *normal_x + this.getBBox().height *normal_y;
        var projected_corner_2 = this.getBBox().width *normal_x + (-this.getBBox().height) *normal_y;

        var total_offset = text_normal_margin + Math.max(Math.abs(projected_corner_1), Math.abs(projected_corner_2));

        var attr =
            {   x : (xfun(d.start)+xfun(d.end))*0.5 + normal_x * total_offset ,
                y : (yfun(d.start)+yfun(d.end))*0.5 + normal_y * total_offset
            };
        if(transTime) d3.select(this).transition().duration(transTime).attr(attr)
        else d3.select(this).attr(attr);
    };

    function textAttribs2(d){
        var dx = xfun(d.end) - xfun(d.start);
        var dy = yfun(d.end) - yfun(d.start);
        var len = Math.sqrt(dx*dx+dy*dy);

        //rotate clockwise
        var normal_x = dy / len;
        var normal_y = -dx / len;

        var projected_corner_1 = this.getBBox().width *normal_x + this.getBBox().height *normal_y;
        var projected_corner_2 = this.getBBox().width *normal_x + (-this.getBBox().height) *normal_y;

        var total_offset = text_normal_margin + Math.max(Math.abs(projected_corner_1), Math.abs(projected_corner_2));

        var attr =
            {   x : (xfun(d.start)+xfun(d.end))*0.5 + normal_x * total_offset,
                y : (yfun(d.start)+yfun(d.end))*0.5 + normal_y * total_offset
            };

        if(transTime) d3.select(this).transition().duration(transTime).attr(attr)
        else d3.select(this).attr(attr);
    };

    /////////////////
    //PRIVILEDGED


    this.clear = function(){
        svg_nodes.selectAll("g").remove();
        svg_links.selectAll("g").remove();
    };

    this.type="GraphDrawer";
    this.graph = Graph.instance;
    this.svgOrigin = svgOrigin;

    var that = this;

    this.screenPosToNodePos = function(pos){
        return {x: that.x.invert(pos[0]-margin.left), y: that.y.invert(pos[1]-margin.top)};
    };

    this.screenPosToTransform = function(pos){
        return "translate(" + (pos[0]-margin.left) + "," + (pos[1]-margin.top) + ")";
    }

    this.updateNodes = function(){
		svg_nodes.selectAll("g").remove();
        // DATA JOIN
        // Join new data with old elements, if any.
          var selection = svg_nodes.selectAll(".node")
            .data(Graph.instance.getNodes(),function(d){return d.id});


        // UPDATE
        // Update old elements as needed.

        // ENTER
        // Create new elements as needed.
          var enterSelection = selection
            .enter().append("g")
            .attr("class","node")
            .call(this.onNodesEntered);//Foo.prototype.setText.bind(bar))
					
            enterSelection.append("circle")
                .attr("r", radius)
                .style("fill",global_NodeLayout['fillStyle'])
                .style("stroke-width",global_NodeLayout['borderWidth'])
                .style("stroke",global_NodeLayout['borderColor'])

            enterSelection.append("text")
                .attr("class","label unselectable")
                .attr("dy", ".35em")           // set offset y position
                .attr("text-anchor", "middle")

			
			enterSelection.append("text")		
                .attr("class","resource unselectable nodeLabel1")
                .attr("dy",function(d){
					if(d.y > 230){
						// set offset y position
						if($("#tabs").tabs('option', 'active') == 2||$("#tabs").tabs('option', 'active') == 4||$("#tabs").tabs('option', 'active') == 5){
							return -global_KnotenRadius - 20 +"px";
						}else if($("#tabs").tabs('option', 'active') == 1||$("#tabs").tabs('option', 'active') == 4 ||$("#tabs").tabs('option', 'active') == 5){
							return -global_KnotenRadius - 10 +"px";
						}						
					}else{
						return -global_KnotenRadius + 45+"px";
					}
				})
				/*.attr("dx", function(d){
					if(d.x > 350){
						return -global_KnotenRadius - 10 +"px";           // set offset y position
					}else{
						return -global_KnotenRadius + 10+"px";
					}
				})*/
                .attr("text-anchor", "middle")
				.style("font-weight", function(d) { return !d.selectedNode ? "" : "bold";})
            .style("fill", function(d){
              if(d.selectedNode){
				  if(d.correct == true){
					  
					return "green";
				  }else if(d.correct == false){
					  return "red";
				  } else {
					  return "blue";
				  }
			  }else{
				  return "black";
              }
            })
            if(transTime){
            selection
                .transition().duration(transTime)
                .attr("transform",transform)
                .call(this.onNodesUpdated);
            }else{
            selection
                .attr("transform",transform)
                .call(this.onNodesUpdated);
            }

            selection.selectAll("text.label")
                 .text(this.nodeLabel);

            var res = selection.selectAll("text.resource")
			.append("tspan");
			res.text(this.nodeText);
			
			
			console.log($("#tabs").tabs('option', 'active'));
			if($("#tabs").tabs('option', 'active') == 2||$("#tabs").tabs('option', 'active') == 4 || $("#tabs").tabs('option', 'active') == 5){ // only show the priorities p in the algorithm Tab and the exercise tabs
				console.log("Im in nodeText2");
				var res1 = selection.selectAll("text.resource")
				.append("tspan")
				.attr("x","0")
				.attr("dy","15");
				res1.text(this.nodeText2);
			}
        // EXIT
        // Remove old elements as needed.
            selection.exit().remove();

    } //end updateNodes()



    this.updateEdges = function(){

        var selection = svg_links.selectAll(".edge")
            .data(Graph.instance.getEdges(),function(d){
                return d.id;
             });

    //ENTER

        var enterSelection = selection
            .enter()
            .append("g")
            .attr("class","edge")
            .call(this.onEdgesEntered);


        enterSelection.append("line")
            .attr("class","arrow")
            .attr("marker-end", "url(#arrowhead2)")
            .style("stroke","black")
            .style("stroke-width",global_Edgelayout['lineWidth'])

        enterSelection.append("text")
//             .style("text-anchor", "middle")
//             .attr("dominant-baseline","middle")
//             .attr("dy", "-.5em")           // set offset y position
            .attr("class","resource unselectable edgeLabel")

        enterSelection.append("text")
//             .style("text-anchor", "middle")
//             .attr("dominant-baseline","middle")
//             .attr("dy", "-.5em")           // set offset y position
            .attr("class","resource unselectable edgeLabel2")


    var that = this;


    //ENTER + UPDATE
        var selt = selection;//.transition().duration(1000);
        selt.selectAll("line")
            .each(lineAttribs)
//             .style("opacity",1e-6)
//             .transition()
//             .duration(750)
//             .style("opacity",1);

        selt.selectAll("text.edgeLabel")
            .text(this.edgeText)
            .style("text-anchor", function(d){
                return "middle";
            })
            .style("font-weight", function(d) { return !d.hin ? "" : "bold";})
            .style("fill", function(d){
              if(d.hin){
				  if(d.correct == true){
					  
					return "green";
				  }else if(d.correct == false){
					  return "red";
				  } else {
					  return "blue";
				  }
			  }else{
				  return "black";
              }
            })
            /*.attr("dominant-baseline",function(d){
                return "text-before-edge";
                //var arrowYProj = d.start.y-d.end.y;
                //return (arrowYProj>0) ? "text-before-edge" : "text-after-edge";
            })*/
            .each(textAttribs)

        selt.selectAll("text.edgeLabel2")
            .text(this.edgeTextBelow)
            .style("text-anchor", function(d){
                return "middle";
            })
			.style("font-weight", function(d) { return !d.rueck ? "" : "bold";})
            .style("fill", function(d){
              if(d.rueck){
				  if(d.correct == true){
					  
					return "green";
				  }else if(d.correct == false){
					  return "red";
				  } else {
					  return "blue";
				  }
			  }else{
				  return "black";
              }
            })
            /*.attr("dominant-baseline",function(d){
                return "text-after-edge";
                //var arrowYProj = d.start.y-d.end.y;
                //return (arrowYProj<0) ? "text-before-edge" : "text-after-edge";
            })*/
            .each(textAttribs2)


        selection.call(this.onEdgesUpdated)

    //EXIT
        var exitSelection = selection.exit()
        exitSelection.remove();

    }


    //initialize //TODO: is called twice when we init both tabs at the same time
    if(Graph.instance==null){
        //calls registered event listeners when loaded;
        var GRAPH_FILENAME = GRAPH_FILENAME || null;
        var filename = GRAPH_FILENAME || "graphs-new/"+$("#tg_select_GraphSelector").val()+".txt"; //the selected option
       Graph.loadInstance(filename,function(error,text,filename){
           console.log("error loading graph instance "+error + " from " + filename +" text: "+text);
       });
    }

} //end constructor GraphDrawer

/**
 * The main function which triggers updates to node and edge selections. 
 */
GraphDrawer.prototype.update= function(){
  this.updateNodes();
  this.updateEdges();
}

/**
 * Called when new nodes are entering
 */
GraphDrawer.prototype.onNodesEntered = function(selection) {
//     console.log(selection[0].length + " nodes entered")
}
/**
 * Called when exisitng nodes are updated
 */
GraphDrawer.prototype.onNodesUpdated = function(selection) {
//     console.log(selection[0].length + " nodes updated")
}
/**
 * Called when new edges are entering
 */
GraphDrawer.prototype.onEdgesEntered = function(selection) {
//     console.log(selection[0].length + " edges entered")
}
/**
 * Called when exisitng edges are updated
 */
GraphDrawer.prototype.onEdgesUpdated = function(selection) {
//     console.log(selection[0].length + " edges entered")
}

/**
 * Displays in the middle of the edge (typically cost/resource vectors or capacity/flow)
 */
GraphDrawer.prototype.edgeText = function(d){
    return d.toString();
}

/**
 * Displays on top of a node (typically constraints or state variables)
 */
GraphDrawer.prototype.nodeText = function(d){
    return d.toString();   
}
/**
 * Displays on top of a node (typically constraints or state variables)
 */
GraphDrawer.prototype.nodeText2 = function(d){
    return d.toString();   
}

/**
 * Displays inside of a node (typically its id)
 */
GraphDrawer.prototype.nodeLabel = function(d){
    return d.id;
}

/**
 * X Position of a node
 */
GraphDrawer.prototype.nodeX = function(d){
    return d.x;
};
/**
 * Y Position of a node
 */
GraphDrawer.prototype.nodeY = function(d){
    return d.y;
};
GraphDrawer.prototype.nodePos = function(d){
    var obj = {};
    obj.x = this.x(this.nodeX(d));
    obj.y = this.y(this.nodeY(d));
    return obj;
}