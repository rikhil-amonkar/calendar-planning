from z3 import *
import json

def main():
    # Define city names and their indices
    city_names = ["Bucharest", "Venice", "Prague", "Frankfurt", "Zurich", "Florence", "Tallinn"]
    # Index mapping: Bucharest:0, Venice:1, Prague:2, Frankfurt:3, Zurich:4, Florence:5, Tallinn:6
    
    # Flight connections as city name pairs
    flight_connections = [
        ("Prague", "Tallinn"),
        ("Prague", "Zurich"),
        ("Florence", "Prague"),
        ("Frankfurt", "Bucharest"),
        ("Frankfurt", "Venice"),  # Note: Venice is spelled as "Venice" in the list, but the connection says "Venice" -> but our city_names has "Venice"
        ("Prague", "Bucharest"),
        ("Bucharest", "Zurich"),
        ("Tallinn", "Frankfurt"),
        ("Zurich", "Florence"),
        ("Frankfurt", "Zurich"),
        ("Zurich", "Venice"),
        ("Florence", "Frankfurt"),
        ("Prague", "Frankfurt"),
        ("Tallinn", "Zurich")
    ]
    
    # Build a connection matrix (7x7) by indices
    conn = [[False] * 7 for _ in range(7)]
    for a, b in flight_connections:
        # Find indices for city names
        try:
            idx_a = city_names.index(a)
        except:
            # Handle Venice: in flight_connections, it's spelled both as "Venice" and "Venice"?
            if a == "Venice":
                idx_a = city_names.index("Venice")
            elif a == "Venice": 
                idx_a = city_names.index("Venice")
            else:
                raise Exception(f"City {a} not found in city_names")
        try:
            idx_b = city_names.index(b)
        except:
            if b == "Venice":
                idx_b = city_names.index("Venice")
            elif b == "Venice":
                idx_b = city_names.index("Venice")
            else:
                raise Exception(f"City {b} not found in city_names")
        conn[idx_a][idx_b] = True
        conn[idx_b][idx_a] = True

    s = Solver()
    
    # Sequence of cities: seq[0] to seq[6] are the indices of the cities in the order of visit
    seq = [Int(f"seq_{i}") for i in range(7)]
    for i in range(7):
        s.add(seq[i] >= 0, seq[i] <= 6)
    s.add(Distinct(seq))
    
    # Flight days: d0, d1, d2, d3, d4, d5 (days when we fly to the next city)
    d0, d1, d2, d3, d4, d5 = Ints('d0 d1 d2 d3 d4 d5')
    
    # Helper function to get required days for a city by its index
    def get_req(idx):
        # Returns the required days for the city index 'idx'
        return If(idx == 0, 3, 
                If(idx == 1, 5,
                If(idx == 2, 4,
                If(idx == 3, 5,
                If(idx == 4, 5,
                If(idx == 5, 5, 5))))))   # idx 6: Tallinn -> 5
    
    # Constraints for the stay lengths
    req0 = get_req(seq[0])
    s.add(d0 == req0)
    
    req1 = get_req(seq[1])
    s.add(d1 == d0 + req1 - 1)
    
    req2 = get_req(seq[2])
    s.add(d2 == d1 + req2 - 1)
    
    req3 = get_req(seq[3])
    s.add(d3 == d2 + req3 - 1)
    
    req4 = get_req(seq[4])
    s.add(d4 == d3 + req4 - 1)
    
    req5 = get_req(seq[5])
    s.add(d5 == d4 + req5 - 1)
    
    req6 = get_req(seq[6])
    s.add(d5 == 27 - req6)   # because 26 - d5 + 1 = req6  => 27 - d5 = req6 => d5 = 27 - req6
    
    # Flight days must be ordered and within [1,26]
    s.add(d0 >= 1, d0 < d1, d1 < d2, d2 < d3, d3 < d4, d4 < d5, d5 <= 26)
    
    # Event constraints:
    # For Venice (city index=1): if it is at position i (0<=i<=5), then d[i] >=22; if at position 6, automatically satisfied (end day=26>=22)
    for i in range(6):  # only for positions 0 to 5
        s.add(If(seq[i] == 1, d[i] >= 22, True))
    
    # For Frankfurt (city index=3): at position i, we require start_day <= 16 and end_day >=12
    for i in range(7):
        start = If(i == 0, 1, d[i-1])
        end = If(i == 6, 26, d[i])
        s.add(If(seq[i] == 3, And(start <= 16, end >= 12), True))
    
    # For Tallinn (city index=6): at position i, we require start_day <= 12 and end_day >=8
    for i in range(7):
        start = If(i == 0, 1, d[i-1])
        end = If(i == 6, 26, d[i])
        s.add(If(seq[i] == 6, And(start <= 12, end >= 8), True))
    
    # Flight connection constraints for consecutive cities in the sequence
    for idx in range(6):
        a = seq[idx]
        b = seq[idx+1]
        # We want conn[a][b] to be True. Since conn is a fixed matrix, create an OR over all (i,j) that are connected.
        cond = []
        for i in range(7):
            for j in range(7):
                if conn[i][j]:
                    cond.append(And(a == i, b == j))
        s.add(Or(cond))
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        # Extract the sequence
        seq_val = [model.evaluate(seq[i]).as_long() for i in range(7)]
        d0_val = model.evaluate(d0).as_long()
        d1_val = model.evaluate(d1).as_long()
        d2_val = model.evaluate(d2).as_long()
        d3_val = model.evaluate(d3).as_long()
        d4_val = model.evaluate(d4).as_long()
        d5_val = model.evaluate(d5).as_long()
        
        d_vals = [d0_val, d1_val, d2_val, d3_val, d4_val, d5_val]
        
        # Build itinerary for 26 days
        itinerary = []
        for day in range(1, 27):  # days 1 to 26
            if day < d0_val:
                pos = 0
            elif day < d1_val:
                pos = 1
            elif day < d2_val:
                pos = 2
            elif day < d3_val:
                pos = 3
            elif day < d4_val:
                pos = 4
            elif day < d5_val:
                pos = 5
            else:
                pos = 6
            city_index = seq_val[pos]
            city_name = city_names[city_index]
            itinerary.append({"day": day, "place": city_name})
        
        # Output as JSON
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()