/**
 * Ford-Fulkerson Algorithmus
 * @author Quirin Fischer
 * @augments GraphDrawer
 * @class
 */
function flowSSPAlgorithm(svgSelection)
{
    GraphDrawer.call(this,svgSelection);

    //insert markers
    var definitions  = svgSelection.append("defs")
        .attr("id", "line-markers");

    definitions.append("marker")
        .attr("id", "flow-arrow")
        .attr("refX",12 ) 
        .attr("refY",2)
        .attr("markerWidth", 12)
        .attr("markerHeight", 4)
        .attr("orient", "auto")
        .append("path")
            .attr("d", "M 0,0 V 4 L6,2 Z")
            .attr("fill", const_Colors.NormalEdgeColor); //this is actual shape for arrowhead

    definitions.append("marker")
        .attr("id", "residual-forward")
        .attr("refX",14) 
        .attr("refY",3)
        .attr("markerWidth", 14)
        .attr("markerHeight", 6)
        .attr("orient", "auto")
        .append("path")
            .attr("d", "M 2,3 L0,6 L8,3 Z")
            .attr("fill", const_Colors.NormalEdgeColor); //this is actual shape for arrowhead

    definitions.append("marker")
        .attr("id", "residual-backward")
        .attr("refX",0) 
        .attr("refY",3)
        .attr("markerWidth", 14)
        .attr("markerHeight", 6)
        .attr("orient", "auto")
        .append("path")
            .attr("d", "M 6,3 L12,3 L14,0 Z")
            .attr("fill", const_Colors.NormalEdgeColor); //this is actual shape for arrowhead


    /**
     * closure for this class
     * @type CycleCancellingAlgorithm
     */
    var that = this;
    var algo = that;
	var bs = new Array();
	var ps = new Array();
	
    var currentFlow = 0;
    var minCost = 0;
	var potentials = [];
	var b = [];
    var debugConsole = true;

    var STEP_SELECTSOURCE = 	    	"select-source";
    var STEP_SELECTTARGET =     		"select-target";
    var STEP_START =            		"start-algorithm";
	var STEP_MAINLOOP =  			    "main-loop";
	var STEP_FINDSHORTESTPATH =			"find-shortestpath";
	var STEP_UPDATEPOTENTIALS = 		"update-potentials";
	var STEP_UPDATECOST = 				"update-cost";
	var STEP_APPLYPATH =        		"apply-augmentation-path";
    var STEP_FINISHED =         		"finished";

    /**
     * the logger instance
     * @type Logger
     */
	var logger = new Logger(d3.select("#logger"));
	
	/** 
	* distance vector with predecessors and distances from s to every other node
	*/
	var distance = new Array();
	
	var del = 0;
	var maxFlow = 0;
	
	/**
	* vector with shortest path from s to t
	*/
	var shortestPath = new Array();
	
	/**
	* Array that contains all the edges in the shortest path
	*/
	var edgesOfSP = new Array();

	var delta = 0;

	var bOfS =0;
	var bOfT =0;
	var usedUpNodes = new Array();
	var edgePrevCost = new Array();
	 /**
     * status variables
     * @type Object
     */
	 
    var state ={
      current_step: STEP_SELECTSOURCE, //status id
      sourceId: -1,
      targetId: -1,
      potentials: [],
	  b: [],
	  distance: [],
	  distancesOfNodes:[],
	  edgesOfSP: [],
	  edgePrevCost: [],
	  anotherEdgeRed: false,
      currentCost: 0
	  
    };

	var mainLoopCounter = 0;
	var edges = new Array();
	
    var colormap = ["#a50026", "#d73027", "#f46d43", "#fdae61", "#fee08b", "#ffffbf", "#d9ef8b", "#a6d96a", "#66bd63", "#1a9850", "#006837"].reverse();

    function flowWidth(val) {
      var edges = Graph.instance.getEdges();
      var capacity = [];
      for (var i =0; i<edges.length; i++){
        capacity[i] = edges[i].resources[0];
      }
        var maxCap = d3.max(capacity);
        return Math.floor(25*(val/maxCap));
    }

    this.flowWidth = flowWidth;

    this.nodeLabel = function(d) {
        if (d.id == state.sourceId)
            return "s";
        else if (d.id == state.targetId)
            return "t";
        else
            return d.id;
    }



    this.nodeText = function(d){
		var res = "b: " + d.b;
		return res;
	};
	
	this.nodeText2 = function(d){

		var pAlternatives;
			if( d.p>=Number.MAX_SAFE_INTEGER-1000000){
				pAlternatives = String.fromCodePoint(8734);
			}else if(d.p<=-Number.MAX_SAFE_INTEGER+1000000 && d.p>=-Number.MAX_SAFE_INTEGER-1000000){
				pAlternatives = "-"+String.fromCodePoint(8734);
			}else{
				pAlternatives = d.p;
			}
		var res = "p: " + pAlternatives;
		return res;
	};
	

	
    this.edgeText = function(d) {
        if(!state.show_residual_graph){
			var cost;
			if( d.resources[1]>=Number.MAX_SAFE_INTEGER-1000000){
				cost = String.fromCodePoint(8734);
			}else if(d.resources[1]<=-Number.MAX_SAFE_INTEGER+1000000 && d.resources[1]>=-Number.MAX_SAFE_INTEGER-1000000){
				cost = "-"+String.fromCodePoint(8734);
			}else if(d.resources[1]<0){
				cost = 0;
			}else{
				cost = d.resources[1];
			}
	
            return "("+d.state.flow+"/"+d.resources[0]+","+cost+")";
		}else{
			var cost;
			if(d.resources[1]>=Number.MAX_SAFE_INTEGER-1000000){
				cost = String.fromCodePoint(8734);
			}else if(d.resources[1]<=-Number.MAX_SAFE_INTEGER+1000000 && d.resources[1]>=-Number.MAX_SAFE_INTEGER-1000000){
				cost = "-"+String.fromCodePoint(8734);
			}else if(d.resources[1]<0){
				cost = 0;
			}else{
				cost = d.resources[1];
			}
            if(d.state.flow < d.resources[0])
                return "(" +(d.resources[0] - d.state.flow) + ", " +cost + ")";
            else
                return "";
        }
    }

    this.edgeTextBelow =
    function(d) {
        if(state.show_residual_graph && d.state.flow > 0){
			var cost;
			if(d.resources[1]>=Number.MAX_SAFE_INTEGER-1000000){
				cost = String.fromCodePoint(8734);
			}else if(d.resources[1]<=-Number.MAX_SAFE_INTEGER+1000000 && d.resources[1]>=-Number.MAX_SAFE_INTEGER-1000000){
				cost = "-"+String.fromCodePoint(8734);
			}else if(d.resources[1]<0){
				cost = 0;
			}else{
				cost = d.resources[1];
			}
            return "(" + d.state.flow + ", " + cost + ")";
		}else
            return "";
    }
	
	
    this.onNodesEntered = function(selection) {
        //select source and target nodes
        selection
        .on("click", function(d) {
            if (state.current_step == STEP_SELECTSOURCE ||
                (state.current_step == STEP_SELECTTARGET && d.id != state.sourceId) )
            {
                that.nextStepChoice(d);
            }
        })

    }

    this.onNodesUpdated = function(selection) {
        selection
        .selectAll("circle")
        .style("fill", function(d) {
            
            if(d.b > 0)
				return const_Colors.StartNodeColor; //green for excess nodes
			else if(d.b < 0)
				return const_Colors.RedText; //red for demand nodes
			else if (d.id == state.sourceId)
                return const_Colors.PQColor; //gelb for start node
            else if (d.id == state.targetId)
                return const_Colors.PQColor;//gelb for end node
			else
                return global_NodeLayout['fillStyle'];

        })


    }


    this.onEdgesEntered = function(selection) {
         selection.append("line")
            .attr("class", "cap")           
			.style("stroke-width",
                    function(d)
                    {
                        return algo.flowWidth(d.resources[0]);
                    })
		 selection.append("line")
            .attr("class", "flow");

    }

    this.onEdgesUpdated = function(selection) {
        selection.selectAll("line.flow")
            .style("stroke-width",
                function(d)
                {
					if(d.inSP)
						return 5;
					else
						return 0;
                });
	 selection.selectAll("line.cap")
           .style("stroke-width",
                 function(d)
                 {
                   if(d.inSP)
						return 5;
					else
						return 0;
				});


        selection.select(".arrow")
            .style("stroke",
                function(d)
                {
					if(d.inSP)
						return "#0000FF";
                    else
                        return "black";
                })

            .attr("marker-end",
                function(d){
                    if(!state.show_residual_graph)
                    {
                        return "url(#flow-arrow)";
                    }
                    else
                    {
                        if(d.resources[0] - d.state.flow > 0)
                            return "url(#residual-forward)";
                        else
                            return "";
                    }
                })
            .attr("marker-start",
                function(d){
                    if(!state.show_residual_graph)
                    {
                        return "";
                    }
                    else
                    {
                        if(d.state.flow > 0)
                            return "url(#residual-backward)";
                        else
                            return "";
                    }
                });


        selection.selectAll("line.cap")
            .style("visibility",
                function()
                {
                    return state.show_residual_graph ? "visible" : "hidden";
                });
        selection.selectAll("line.flow")
            .style("visibility",
                function()
                {
                    return state.show_residual_graph ? "visible": "hidden";
                });

    }


    /**
     * Replay Stack, speichert alle Schritte des Ablaufs für Zurück Button
     * @type {Array}
     */
    var replayHistory = new Array();

    var fastforwardOptions = {label: $("#ta_button_text_fastforward").text(), icons: {primary: "ui-icon-seek-next"}};

    /**
     * Initialisiert das Zeichenfeld
     * @method
     */
    this.init = function() {

        Graph.addChangeListener(function(){
            that.clear();
            that.reset();
            that.squeeze();
            that.update();
        });

        this.reset();
        this.update();
    };
	
	var initialCost = new Array();
	
    /**
     * clear all states
     */
    this.reset = function(){
        state = {
			current_step: STEP_SELECTSOURCE, //status id
			sourceId: -1,
			targetId: -1,
			shortestPath: [],
			distance: [],
			distancesOfNodes:[],
			edgePrevCost: [],
			anotherEdgeRed: false,
			currentCost: 0
        };
		usedUpNodes = new Array();
		del=0;
		edgesOfSP = new Array();
		distance = new Array();
		mainLoopCounter =0;
		edges = new Array();
        this.replayHistory = [];
        this.currentFlow= 0;
        this.minCost = 0;
        if(Graph.instance){
            //prepare graph for this algorithm: add special properties to nodes and edges
            Graph.instance.nodes.forEach(function(key, node) {
                node.state.predecessor = null;
                node.b = 0;
				node.p = 0;
				bs[node.id] = node.b;
				ps[node.id] = node.p;
				node.isUsedUp = false;
            })

            Graph.instance.edges.forEach(function(key, edge) {
                edge.state.flow = 0;
				edge.inSP = false;
				edge.state.usedUp = false;
				if(mainLoopCounter >1){
					edge.resources[1] = initialCost[edge.id];
					
				}
            });

        }
    }

    /**
     * Makes the view consistent with the state
     * @method
     */
    this.update = function(){

        this.updateDescriptionAndPseudocode();
        this.updateVariableState();
        this.updateGraphState();
        logger.update();

        if(Graph.instance){
             flowSSPAlgorithm.prototype.update.call(this); //updates the graph
        }
    }

    /**
     * When Tab comes into view
     * @method
     */
    this.activate = function() {
		Graph.instance.edges.forEach(function(key,edge){
			initialCost[edge.id] = edge.resources[1];
		});
        this.reset();
        this.squeeze();
        this.update();

    };
	

	/**
     * tab disappears from view
     * @method
     */
    this.deactivate = function() {

		Graph.instance.edges.forEach(function(key,edge){
			
			edge.resources[1] = initialCost[edge.id];
			
		});
		this.reset();
		Graph.instance.nodes.forEach(function(key,node){
			node.state.distance = Number.MAX_SAFE_INTEGER;
		});
		minCost = 0;
		this.clear();
        this.stopFastForward();
        this.replayHistory = [];

		
    };

    /**
     * add a step to the replay stack, serialize stateful data
     * @method
     */
    this.addReplayStep = function() {
			
		var seen =  [];
			
		Graph.instance.edges.forEach(function(key,edge){
			state.edgePrevCost[edge.id] = edge.resources[1];
		});
        replayHistory.push({
            "graphState": Graph.instance.getState(),
			"minCost" : minCost,
			
            "state": JSON.stringify(state, function(key, val) {
				if (val != null && typeof val == "object") {
					if (seen.indexOf(val) >= 0) {
						return;
					}
					seen.push(val);
				}
				return val;
			}),
			"del" : del,
			
            "legende": $("#tab_ta").find(".LegendeText").html(),
            "loggerData": JSON.stringify(logger.data),
			"mainLoopCounter": mainLoopCounter
        });

        if (debugConsole)
            console.log("Current History Step: ", replayHistory[replayHistory.length - 1]);

    };
	
	
	
    /**
     * playback the last step from stack, deserialize stateful data
     * @method
     */
    this.previousStepChoice = function() {

        var oldState = replayHistory.pop();
        if (debugConsole)
            console.log("Replay Step", oldState);
		
        Graph.instance.setState(oldState.graphState);
		mainLoopCounter = oldState.mainLoopCounter;
					
			Graph.instance.edges.forEach(function(key,edge){	
				edge.resources[1] = state.edgePrevCost[edge.id];
				
			});
		if(state.current_step == STEP_MAINLOOP){
			Graph.instance.nodes.forEach(function(key,node){
				node.b = bs[node.id];
				
			});
		}

		if(state.current_step == STEP_SELECTSOURCE || state.current_step == STEP_SELECTTARGET || state.current_step == STEP_START){
			Graph.instance.nodes.forEach(function(key,node){
				node.b = 0;
				bs[node.id] = node.b;
				node.p = 0;
				ps[node.id] = node.p;
			});
			
		}
		if(state.current_step == STEP_UPDATECOST){
			Graph.instance.nodes.forEach(function(key,node){
				node.p = ps[node.id];
				
			});
		}

		Graph.instance.edges.forEach(function(key,edge){		
			if($.inArray(edge, state.edgesOfSP) != -1){
				edge.inSP = true;
			}else{
				edge.inSP = false;
			}
		});

		var seen = [];
		state = JSON.parse(oldState.state, function(key, val) {
			if (val != null && typeof val == "object") {
				if (seen.indexOf(val) >= 0) {
					return;
				}
				seen.push(val);
			}
			return val;
		});
        logger.data = JSON.parse(oldState.loggerData);
		del = oldState.del;
		minCost = oldState.minCost;		
		
        $("#tab_ta").find(".LegendeText").html(oldState.legende);
		
        this.update();
    };

    /**
     * updates status description and pseudocode highlight based on current step
     * @method
     */
    this.updateDescriptionAndPseudocode = function() {
        var sel = d3.select("#ta_div_statusPseudocode").selectAll("div");
        sel.classed("marked", function(a, pInDivCounter, divCounter) {
            return d3.select(this).attr("id") === "pseudocode-"+state.current_step;
        });

        var sel = d3.select("#ta_div_statusErklaerung").selectAll("div");
        sel.style("display", function(a, divCounter) {
            return (d3.select(this).attr("id") === "explanation-"+state.current_step) ? "block" : "none";
        });

        var disable_back_button = state.current_step === STEP_SELECTSOURCE;
        var disable_forward_button =
                        (state.current_step === STEP_SELECTSOURCE ||
                        state.current_step === STEP_SELECTTARGET ||
                        state.current_step === STEP_FINISHED);
        var disable_fastforward_button =
                        (state.current_step === STEP_SELECTSOURCE ||
                        state.current_step === STEP_SELECTTARGET ||
                        state.current_step === STEP_FINISHED);

        $("#ta_button_Zurueck").button("option", "disabled", disable_back_button);
        $("#ta_button_1Schritt").button("option", "disabled", disable_forward_button);
        $("#ta_button_vorspulen").button("option", "disabled", disable_fastforward_button);
    };

    this.updateGraphState = function()
    {
        var state_label = "";
        var currMinCost = "";
        if(state.show_residual_graph){
            state_label = "Residual network";
        }else{
          state_label = "Network"
        }
        if(state.current_step == STEP_FINISHED){
          currMinCost = "Minimal cost: " + minCost;
        }else{
          currMinCost = "Current cost: " + minCost;
        }
        d3.select("#graph-state").text(state_label);
        d3.select("#cost-info").text(currMinCost)
        d3.select("#graph-info").style("display", state.show_residual_graph ? "block" : "block");
    }

    this.updateVariableState = function()
    {	
        var sp_edge_strings = [];
        for(var i = 0; i<state.shortestPath.length-1; i++){

            var edge_string = "";
            if(state.shortestPath[i] == state.sourceId)
                edge_string+= "s";
            else if(state.shortestPath[i] == state.targetId)
                edge_string += "t";
            else
                edge_string += state.shortestPath[i];

            edge_string += "->"

            if(state.shortestPath[i+1] == state.sourceId)
                edge_string += "s";
            else if(state.shortestPath[i+1] == state.targetId)
                edge_string += "t";
            else
                edge_string += state.shortestPath[i+1];

            sp_edge_strings.push(edge_string);
        }
        var sp_string = "["+sp_edge_strings.join(",")+"]";
		var distances_string = "("+state.distancesOfNodes.join(",")+")";
        d3.select("#variable-value-shortestPath").text(sp_string);
		d3.select("#variable-value-delta").text(del);
		d3.select("#variable-value-distances").text(distances_string);
        d3.select("#finalflow").text(maxFlow);
        d3.select("#minCost").text(minCost);
		d3.select("#bs").text(bOfS);
		d3.select("#bt").text(bOfT);

    }
	
    ///////////////////////Actual algorithm steps

    /**
     * Executes the next step in the algorithm
     * @method
     */
    this.nextStepChoice = function(d)
    {
		
        if (debugConsole)
            console.log("State Before: " + state.current_step);

        // Speichere aktuellen Schritt im Stack
        this.addReplayStep();
	
        switch (state.current_step) {
            case STEP_SELECTSOURCE:
                this.selectSource(d);
                break;
            case STEP_SELECTTARGET:
                this.selectTarget(d);
                break;
            case STEP_START:
				minCost = 0;
                logger.log("Now the algorithm can start");
                state.current_step = STEP_MAINLOOP;
				state.show_residual_graph = true;
				getMaxFlow();
				
                break;
			case STEP_MAINLOOP:
				mainLoop();
				break;
			case STEP_FINDSHORTESTPATH:
                findShortestPath();
                break;
            case STEP_UPDATEPOTENTIALS:
                updatePotentials();
                break;
            case STEP_UPDATECOST:
                updateCost();
                break;
            case STEP_APPLYPATH:
                applyPath();
                break;
            case STEP_FINISHED:
                this.stopFastForward();
                break;
            default:
                console.log("Fehlerhafter State");
                break;
        }
        if (debugConsole)
            console.log("State After: " + state.current_step);

        //update view with status values
        this.update();
    };


    /**
     * select the source node
     */
    this.selectSource = function(d)
    {
        state.sourceId = d.id;
        state.current_step = STEP_SELECTTARGET;
        logger.log("selected node " + d.id + " as source");
    };

	
    /**
     * select the target node
     */
    this.selectTarget = function(d)
    {
        state.targetId = d.id;
        state.current_step = STEP_START;
        logger.log("selected node " + d.id + " as target");
    };



    /**
	* Initializes maximal Flow and stores it in the variable currentFlow which is then used to initialize the excess/demand of the nodes s and t.
	*/
    function getMaxFlow()
    {

        Graph.instance.edges.forEach(
            function(key, edge)
            {
                edge.state.flow = 0;
            })

        var no_path_found = false;
        currentFlow = 0;
        while(!no_path_found)
        {
            Graph.instance.nodes.forEach(
                function(key, node)
                {
                    node.state.predecessor = null;
                });
            var search_queue = [state.sourceId];
            var source = Graph.instance.nodes.get(state.sourceId);
            source.state.predecessor = {};
            while(Graph.instance.nodes.get(state.targetId).state.predecessor == null && search_queue.length > 0 )
            {
                var node_to_expand = search_queue.shift();
                var node = Graph.instance.nodes.get(node_to_expand);
                var out_edges = node.getOutEdges();
                for (var i = 0; i < out_edges.length; i++)
                {
                    var edge_out = out_edges[i];

                    if(edge_out.end.state.predecessor == null && edge_out.resources[0] > edge_out.state.flow)
                    {
                        search_queue.push(edge_out.end.id);
                        edge_out.end.state.predecessor =
                            {
                                "node": node_to_expand,
                                "edge": edge_out.id,
                                "residual-capacity":edge_out.resources[0] - edge_out.state.flow,
                                "direction": 1
                            };
                    }
                }

                var in_edges = node.getInEdges();
                for (var i = 0; i < in_edges.length; i++)
                {
                    var edge_in = in_edges[i];

                    if(edge_in.start.state.predecessor == null && edge_in.state.flow > 0)
                    {
                        search_queue.push(edge_in.start.id);
                        edge_in.start.state.predecessor =
                            {
                                "node": node_to_expand,
                                "edge": edge_in.id,
                                "residual-capacity": edge_in.state.flow,
                                "direction": -1
                            };
                    }
                }
            }

            if(Graph.instance.nodes.get(state.targetId).state.predecessor != null)
            {
                var path = [];
                var augmentation = Number.MAX_SAFE_INTEGER;
                var next_path_node = state.targetId;

                //gather path
                while(next_path_node != state.sourceId)
                {
                    var node = Graph.instance.nodes.get(next_path_node);
                    path.push(node.state.predecessor);
                    augmentation = Math.min(node.state.predecessor["residual-capacity"], augmentation);
                    next_path_node = node.state.predecessor["node"];
                }

                //apply path
                for (var i = 0; i < path.length; i++)
                {
                    var predecessor = path[i];
                    var edge = Graph.instance.edges.get(predecessor["edge"]);
                    edge.state.flow += predecessor["direction"] * augmentation;

                }
                currentFlow += augmentation;


            }
            else
                no_path_found = true;
        }
		maxFlow = currentFlow;
        Graph.instance.nodes.forEach(
            function(key, node){
				bs[node.id] = node.b;
                if(node.id == state.sourceId){
					node.b = currentFlow;
					bOfS = node.b;
				}else if(node.id == state.targetId){
					node.b = -currentFlow;
					bOfT = node.b;
				}else{
					node.b = 0;
				}
			});
			
			Graph.instance.edges.forEach(
            function(key, edge)
            {
                edge.state.flow = 0;
            })

        var no_path_found = false;
        currentFlow = 0;
        state.current_step = STEP_MAINLOOP;
        logger.log("Init of maxflow.");

    }


    
	/**
	* main loop: checks if s is still an exces node. 
	*			 If if is: run the loop steps; 
	*		     If it is not: the algorithm terminates.
	* @method	
	*/
    function mainLoop()
    {
		mainLoopCounter++;
        if (Graph.instance.nodes.get(state.sourceId).b == 0) {
            state.current_step = STEP_FINISHED; //so that we display finished, not mainloop when done
            that.stopFastForward();
            
            logger.log("Finished with a min cost of "+ minCost);

        }
        else
        {
            logger.log("Not finished, starting search for augmentation cycle ");
            state.show_residual_graph = true;
            state.current_step = STEP_FINDSHORTESTPATH;         
		
        }
    }
		
	
	/**
	* Implementation of the Bellman-Ford algorithm. 
	* Finds the shortest distances from s to every node in the graph and the shortest path from s to t.
	* @method
	*/
	function findShortestPath(){
		state.edgesOfSP = [];
		state.shortestPath = [];
				
		Graph.instance.nodes.forEach(
            function(key, node)
            {
								
				node.state.distance = Number.MAX_SAFE_INTEGER;
				node.state.predecessor = null;
            });

        var target  = Graph.instance.nodes.get(state.targetId);
        target.state.distance = Number.MAX_SAFE_INTEGER;
		var source  = Graph.instance.nodes.get(state.sourceId);
		source.state.distance = 0;
		source.state.predecessor = {
			"prev_node": state.sourceId,
			"direction": 1
		}
		
		var usedUpEdges=new Array();
	
		for(var i = 0; i < Graph.instance.nodes.size(); i++){
			Graph.instance.edges.forEach(function(key,edge){
				var edge_startnode = edge.start;
				var edge_endnode = edge.end;

				if(!edge.state.usedUp && edge_endnode.usedUp == false && edge_startnode.usedUp == false){
					
					if(edge.resources[0] - edge.state.flow > 0){
						if(edge.state.flow > 0){
							
							if(edge_endnode.state.distance - edge.state.cost < edge_startnode.state.distance){
								
								edge_startnode.state.distance = edge_endnode.state.distance - edge.resources[1];
								
								
								edge_startnode.state.predecessor = {
									"edge_id": edge.id*(-1)-1,
									"prev_node": edge_endnode.id,
									"direction": -1
								};
							}
							
						}
						if(edge_startnode.state.distance + edge.resources[1] < edge_endnode.state.distance){
							
							edge_endnode.state.distance = edge_startnode.state.distance + edge.resources[1];
	
							
							edge_endnode.state.predecessor = {
										"edge_id": edge.id,
										"prev_node": edge_startnode.id,
										"direction": 1
							};
																  
						}

					}
				}
						
			});
			Graph.instance.edges.forEach(function(key,edge){
				var edge_startnode = edge.start;
				var edge_endnode = edge.end;
				var numberOfUsedUp = 0;
				
					if (edge.state.usedUp){
						usedUpEdges.push(edge);
						var inE = edge_endnode.getInEdges();
	
						
						for(var i = 0; i<inE.length; i++){
							if(inE[i].state.usedUp){
								numberOfUsedUp++;
							}
						}
						
						if(numberOfUsedUp != inE.length){
							inE.filter(function(e){
								return !e.state.usedUp;
							});
							
							inE.sort(function(a,b){
									return (a.resources[1]) - (b.resources[1]);
							});
								
							var e;
							var id=-1;
							for(var i = 0; i<inE.length; i++){
						
								if(inE[i].start.predecessor == null){

									inE[i].start.state.distance = 0;
									inE[i].start.state.predecessor = {
										"edge_id" : inE[i].id,
										"prev_node": inE[i].start.id,
										"direction" : 1
									}	
									
								}
								
								if(!inE[i].state.usedUp && inE[i].start.state.predecessor["direction"] == 1){
									id = i;	
									e = inE[id];
									break;
								}
							}
							if(id != -1){
						
								edge_endnode.state.distance = edge_startnode.state.distance + e.resources[1];
								edge_endnode.state.predecessor = {
											"edge_id": e.id,
											"prev_node": inE[id].start.id,
											"direction": 1
								}
								
							}else{
								edge_endnode.state.distance = edge_startnode.state.distance + edge.resources[1];
								edge_endnode.state.predecessor = {
											"edge_id": edge.id,
											"prev_node": edge.start.id,
											"direction": 1
								}
								
							}
						}else{
							
							edge_endnode.usedUp = true;
							edge_endnode.state.distance = edge_startnode.state.distance + edge.resources[1];
							usedUpNodes.push(edge_endnode);
						}
						
					}		
			});

		}	
			
		//backtrack to find SP from s to t
		var temp = Graph.instance.nodes.get(state.targetId);	
			
		while(temp.id != state.sourceId && 
		$.inArray(state.sourceId, state.shortestPath.reverse()) != 0 &&
		temp.state.predecessor["prev_node"] != state.targetId){
			

		state.shortestPath.reverse();
		
		if($.inArray(temp.id, state.shortestPath) == -1){

			var inEdgesForTemp = temp.getInEdges();
			
			for(var k = 0; k<inEdgesForTemp.length; k++){
				
				var tempSP = state.shortestPath;
			
				if(tempSP.filter(function(e) { return e == inEdgesForTemp[k].start.id; }).length > 0  || inEdgesForTemp[k].start.id == state.targetId ||  
				inEdgesForTemp[k].state.usedUp || 
				inEdgesForTemp[k].start.usedUp){
					
					inEdgesForTemp.splice(k,1);
				}
				
			}
			inEdgesForTemp.sort(function(a,b){
					
					return (a.start.state.distance + a.resources[1]) - (b.start.state.distance+b.resources[1]);
				
			});
			

			if(inEdgesForTemp.length == 0)
				return;
			else{
				temp.state.distance = inEdgesForTemp[0].start.state.distance + inEdgesForTemp[0].resources[1];
				temp.state.predecessor["prev_node"] = inEdgesForTemp[0].start.id;
				temp.state.predecessor["edge_id"] = inEdgesForTemp[0].id;
				temp.state.predecessor["diresction"] = 1;					
			}
		}
							

			state.shortestPath.unshift(temp.id);
			
			state.shortestPath.unshift(temp.state.predecessor["prev_node"]);
			var temp1 = temp;
			temp = Graph.instance.nodes.get(temp.state.predecessor["prev_node"]);
			
			if(temp.state.predecessor["prev_node"] == state.sourceId){
				
				state.shortestPath.unshift(temp.state.predecessor["prev_node"]);
				break;
			
			}else if($.inArray(temp.state.predecessor["prev_node"],state.shortestPath)!=-1 || 
					temp.state.predecessor["prev_node"] == temp1.id || 
					temp.state.predecessor["prev_node"] == state.targetId ||
					temp.state.predecessor["prev_node"]){
						
				
				var inEdgesForTemp = temp.getInEdges();
				
				for(var k = 0; k<inEdgesForTemp.length; k++){

					var tempSP = state.shortestPath;

					
					if(tempSP.filter(function(e) { return e == inEdgesForTemp[k].start.id; }).length > 0  || inEdgesForTemp[k].start.id == state.targetId ||  
					inEdgesForTemp[k].state.usedUp || 
					inEdgesForTemp[k].start.usedUp){
						
						inEdgesForTemp.splice(k,1);
					}
				}
				

				inEdgesForTemp.sort(function(a,b){

						return (a.start.state.distance + a.resources[1]) - (b.start.state.distance+b.resources[1]);
					
				});
				

				if(inEdgesForTemp.length == 0)
					return;
				else{
					temp.state.predecessor["prev_node"] = inEdgesForTemp[0].start.id;
					if(temp.state.predecessor["prev_node"] == state.sourceId){
						temp.state.distance = inEdgesForTemp[0].start.state.distance + inEdgesForTemp[0].resources[1];
						temp.state.predecessor["prev_node"] = inEdgesForTemp[0].start.id;
						temp.state.predecessor["edge_id"] = inEdgesForTemp[0].id;
						temp.state.predecessor["diresction"] = 1;
						state.shortestPath.unshift(temp.state.predecessor["prev_node"]);
						break;
					}
				}
				
			}	
					
		}
		
		Graph.instance.nodes.forEach(function(key,node){
			state.distancesOfNodes.push(node.state.distance);
		});

		for(var j = 1; j<state.shortestPath.length; j++){
			
			Graph.instance.edges.forEach(function(key,edge){
					if(edge.start.id == state.shortestPath[j-1] && edge.end.id == state.shortestPath[j]){
						edge.inSP = true;
						state.edgesOfSP.push(edge);
						edge.start.state.predecessor["direction"] = 1;
					}			
			});
		}
		
		state.current_step = STEP_UPDATEPOTENTIALS;
	}

	/**
	* Updates the potentials p_new(v) = p_old(v) - distance(s,v) for every node v in the graph 
	* @method
	*/
	function updatePotentials(){
		Graph.instance.edges.forEach(function(key,edge){
			state.edgePrevCost[edge.id] = edge.resources[1];
		});
		Graph.instance.nodes.forEach(function(key,node){
			ps[node.id] = node.p;
			node.p = node.p - node.state.distance;
		});
		state.current_step = STEP_UPDATECOST;
		
	}
	
	/**
	* Updates the costs for each edge with respect to the 
	* @method
	*/
	function updateCost(){

		Graph.instance.edges.forEach(function(key,edge){
			state.edgePrevCost[edge.id] = edge.resources[1];
			if(mainLoopCounter == 1){
				edge.edges = {
					"cost": edge.resources[1],
					"cap": edge.resources[0],
					"id": edge.id
					
				};
			}
			//if(edge.resources[1] > 0){
				edge.resources[1] = initialCost[edge.id] - edge.start.p + edge.end.p;
			//}
			
		});
		var cap = [];
		for (var i =0; i<state.edgesOfSP.length; i++){
			
			cap[i] = state.edgesOfSP[i].resources[0]-state.edgesOfSP[i].state.flow;
			
		}
		var minCap = d3.min(cap);
		var minED = Math.min(Graph.instance.nodes.get(state.sourceId).b , -Graph.instance.nodes.get(state.targetId).b);
		
		state.current_step = STEP_APPLYPATH;
		del = Math.min(minCap,minED);
	}
	

	/**
	* Calculates the maximal possible flow delta that can be augmented through the shortest path and
	* augments delta flow units along the shortest path
	* @method
	*/
	function applyPath(){
		var cap = [];
		delta = 0;
		Graph.instance.edges.forEach(function(key,edge){
			state.edgePrevCost[edge.id] = edge.resources[1];
		});
		for (var i =0; i<state.edgesOfSP.length; i++){
			
			cap[i] = state.edgesOfSP[i].resources[0]-state.edgesOfSP[i].state.flow;
			
		}
        var minCap = d3.min(cap);
		
		var excessDemandMin = Math.min(Graph.instance.nodes.get(state.sourceId).b , -Graph.instance.nodes.get(state.targetId).b);
		delta = Math.min(minCap, excessDemandMin);
		
	
		for (var i = 0; i < state.edgesOfSP.length; i++){
           
            var edge = state.edgesOfSP[i];

            edge.state.flow += edge.start.state.predecessor["direction"] * delta;
			minCost += delta * edge.edges["cost"];
        }
		Graph.instance.nodes.forEach(function(key,node){
			bs[node.id] = node.b;
			if(node.id == state.sourceId){
				node.b = node.b-delta;
				bOfS = node.b;
			}else if(node.id == state.targetId){
				node.b = node.b + delta;
				bOfT = node.b;
				
			}else{
				node.b = 0;
			}
		});
		
		Graph.instance.edges.forEach(function(key, edge) {
			edge.inSP = false;
			if(edge.state.flow == edge.resources[0]){
				edge.state.usedUp = true;	
			}else{
				edge.state.usedUp = false;	

			}
        });
        logger.log("Applied augmenting path with flow "+state.augmentation);
		del = 0;
		state.distancesOfNodes = [];
        state.show_residual_graph = false;
		state.shortestPath = [];
        state.current_step = STEP_MAINLOOP;
		
	}
	

	this.getWarnBeforeLeave = function(){
		if(state.current_step == STEP_SELECTSOURCE || state.current_step == STEP_FINISHED){
			return false;
		}
		return true;
	}
}

// Vererbung realisieren
flowSSPAlgorithm.prototype = Object.create(GraphDrawer.prototype);
flowSSPAlgorithm.prototype.constructor = flowSSPAlgorithm;
