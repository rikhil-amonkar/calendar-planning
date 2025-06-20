from z3 import *

def main():
    # City indices: 0:Geneva, 1:Munich, 2:Valencia, 3:Bucharest, 4:Stuttgart
    city_names = ["Geneva", "Munich", "Valencia", "Bucharest", "Stuttgart"]
    durations = [4, 7, 6, 2, 2]
    
    # Allowed direct flight edges (undirected)
    allowed_edges = [
        (0,1), (1,0),
        (1,2), (2,1),
        (3,2), (2,3),
        (1,3), (3,1),
        (2,4), (4,2),
        (0,2), (2,0)
    ]
    
    # Position variables for the sequence
    pos0, pos1, pos2, pos3, pos4 = Ints('pos0 pos1 pos2 pos3 pos4')
    pos = [pos0, pos1, pos2, pos3, pos4]
    
    s = Solver()
    
    # Each position must be between 0 and 4
    for p in pos:
        s.add(p >= 0, p <= 4)
    
    # All positions must be distinct
    s.add(Distinct(pos0, pos1, pos2, pos3, pos4))
    
    # Function to get duration of a city index
    def dur(city_idx):
        return If(city_idx == 0, 4,
               If(city_idx == 1, 7,
               If(city_idx == 2, 6,
               If(city_idx == 3, 2, 2))))
    
    d_vals = [dur(p) for p in pos]
    
    # Cumulative sums for the first i cities (for i from 0 to 4)
    # S[0] = 0, S[1] = d0, S[2] = d0+d1, S[3] = d0+d1+d2, S[4] = d0+d1+d2+d3
    S = [0] 
    for i in range(4):
        S.append(S[-1] + d_vals[i])
    
    # Start days for each city in the sequence
    starts = [1]  # start of first city is day 1
    for i in range(1, 5):
        starts.append(1 + S[i] - i)
    
    # Constraints for Geneva and Munich
    for i in range(5):
        s.add(If(pos[i] == 0, starts[i] <= 4, True))
        s.add(If(pos[i] == 1, starts[i] <= 10, True))
    
    # Flight connection constraints between consecutive cities
    for i in range(4):
        edge_constraints = []
        for a, b in allowed_edges:
            edge_constraints.append(And(pos[i] == a, pos[i+1] == b))
        s.add(Or(edge_constraints))
    
    if s.check() == sat:
        m = s.model()
        order = [m.evaluate(p).as_long() for p in pos]
        fixed_durations = [4, 7, 6, 2, 2]
        
        # Compute start days based on the resolved order
        cum = 0
        computed_starts = [1]
        for i in range(1, 5):
            cum += fixed_durations[order[i-1]]
            computed_starts.append(1 + cum - i)
        
        itinerary = []
        for i in range(5):
            city_idx = order[i]
            name = city_names[city_idx]
            s_day = computed_starts[i]
            dur_val = fixed_durations[city_idx]
            e_day = s_day + dur_val - 1
            
            if i == 0:
                itinerary.append({"day_range": f"Day {s_day}-{e_day}", "place": name})
                if i < 4:
                    itinerary.append({"day_range": f"Day {e_day}", "place": name})
            else:
                itinerary.append({"day_range": f"Day {s_day}", "place": name})
                itinerary.append({"day_range": f"Day {s_day}-{e_day}", "place": name})
                if i < 4:
                    itinerary.append({"day_range": f"Day {e_day}", "place": name})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()