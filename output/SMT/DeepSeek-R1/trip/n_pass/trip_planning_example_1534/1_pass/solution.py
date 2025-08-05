from z3 import *
import json

def main():
    # City names and their global indices
    city_index = {
        'Paris': 0,
        'Warsaw': 1,
        'Venice': 2,
        'Vilnius': 3,
        'Salzburg': 4,
        'Amsterdam': 5,
        'Barcelona': 6,
        'Hamburg': 7,
        'Florence': 8,
        'Tallinn': 9
    }
    index_to_city = {v: k for k, v in city_index.items()}
    
    # Durations for each city
    durations_dict = {
        'Paris': 2,
        'Warsaw': 4,
        'Venice': 3,
        'Vilnius': 3,
        'Salzburg': 4,
        'Amsterdam': 2,
        'Barcelona': 5,
        'Hamburg': 4,
        'Florence': 5,
        'Tallinn': 2
    }
    
    # Parse flight connections
    flights_str = "Paris and Venice, Barcelona and Amsterdam, Amsterdam and Warsaw, Amsterdam and Vilnius, Barcelona and Warsaw, Warsaw and Venice, Amsterdam and Hamburg, Barcelona and Hamburg, Barcelona and Florence, Barcelona and Venice, Paris and Hamburg, Paris and Vilnius, Paris and Amsterdam, Paris and Florence, Florence and Amsterdam, Vilnius and Warsaw, Barcelona and Tallinn, Paris and Warsaw, Tallinn and Warsaw, from Tallinn to Vilnius, Amsterdam and Tallinn, Paris and Tallinn, Paris and Barcelona, Venice and Hamburg, Warsaw and Hamburg, Hamburg and Salzburg, Amsterdam and Venice"
    flight_pairs = set()
    for item in flights_str.split(','):
        item = item.strip()
        if "from " in item and " to " in item:
            parts = item.split()
            a = parts[1]
            b = parts[3]
            flight_pairs.add((a, b))
        elif " and " in item:
            parts = item.split(" and ")
            a = parts[0].strip()
            b = parts[1].strip()
            flight_pairs.add((a, b))
    
    allowed_global_pairs = set()
    for (a, b) in flight_pairs:
        if a in city_index and b in city_index:
            i1 = city_index[a]
            i2 = city_index[b]
            allowed_global_pairs.add((i1, i2))
            allowed_global_pairs.add((i2, i1))
    
    # Define the 7 variable cities (positions 1-7)
    city_list = ['Amsterdam', 'Barcelona', 'Florence', 'Tallinn', 'Venice', 'Vilnius', 'Warsaw']
    durations_local = [durations_dict[city] for city in city_list]
    global_index_list = [city_index[city] for city in city_list]  # [5, 6, 8, 9, 2, 3, 1]
    
    # Z3 solver setup
    s = Solver()
    
    # Variables for positions 1-7
    v = [Int(f'v{i}') for i in range(1, 8)]
    for var in v:
        s.add(var >= 0, var <= 6)
    s.add(Distinct(v))
    
    # Global indices for positions 1-7
    g = [Int(f'g{i}') for i in range(1, 8)]
    for i in range(7):
        for j in range(7):
            s.add(If(v[i] == j, g[i] == global_index_list[j], True))
    
    # Durations for all positions (0-9)
    d = [Int(f'd{i}') for i in range(10)]
    s.add(d[0] == durations_dict['Paris'])   # Position 0: Paris
    s.add(d[8] == durations_dict['Hamburg']) # Position 8: Hamburg
    s.add(d[9] == durations_dict['Salzburg']) # Position 9: Salzburg
    for i in range(1, 8):  # Positions 1-7
        for j in range(7):
            s.add(If(v[i-1] == j, d[i] == durations_local[j], True))
    
    # Cumulative sums
    cum = [Int(f'cum{i}') for i in range(11)]
    s.add(cum[0] == 0)
    for i in range(1, 11):
        s.add(cum[i] == cum[i-1] + (d[i-1] - 1))
    
    # Fixed cumulative constraints
    s.add(cum[8] == 18)  # For Hamburg at position 8
    s.add(cum[10] == 24)  # Total cumulative sum
    
    # Barcelona and Tallinn constraints
    for i in range(1, 8):  # Positions 1-7
        # Barcelona (local index 1) constraint: cum[i] <= 5
        s.add(If(v[i-1] == 1, cum[i] <= 5, True))
        # Tallinn (local index 3) constraint: 9 <= cum[i] <= 11
        s.add(If(v[i-1] == 3, And(cum[i] >= 9, cum[i] <= 11), True))
    
    # Flight constraints for edges 0-7
    # Edge 0: Paris (0) to position 1 (g[0])
    allowed_after_0 = [b for (a, b) in allowed_global_pairs if a == 0]
    s.add(Or([g[0] == b for b in allowed_after_0]))
    
    # Edges 1-6: between variable positions
    for edge in range(1, 7):
        from_index = g[edge-1]
        to_index = g[edge]
        constraints = []
        for (a, b) in allowed_global_pairs:
            constraints.append(And(from_index == a, to_index == b))
        s.add(Or(constraints))
    
    # Edge 7: position 7 (g[6]) to Hamburg (7)
    from_index = g[6]
    to_index = 7
    constraints = []
    for (a, b) in allowed_global_pairs:
        constraints.append(And(from_index == a, to_index == b))
    s.add(Or(constraints))
    
    # Solve the model
    if s.check() == sat:
        model = s.model()
        # Get the assignment for v[0..6]
        v_vals = [model.eval(var).as_long() for var in v]
        # Get the global indices for positions 1-7
        g_vals = [model.eval(g_var).as_long() for g_var in g]
        # Get the durations for positions 0-9
        d_vals = [model.eval(d_var).as_long() for d_var in d]
        # Get cumulative sums
        cum_vals = [model.eval(c_var).as_long() for c_var in cum]
        
        # Map positions to city names
        city_at_position = [None] * 10
        city_at_position[0] = 'Paris'
        city_at_position[8] = 'Hamburg'
        city_at_position[9] = 'Salzburg'
        for i in range(1, 8):
            city_at_position[i] = city_list[v_vals[i-1]]
        
        # Build itinerary: list of (day, city)
        itinerary_list = []
        for pos in range(10):
            city_name = city_at_position[pos]
            start_day = 1 + cum_vals[pos]
            duration = d_vals[pos]
            end_day = start_day + duration - 1
            for day in range(start_day, end_day + 1):
                itinerary_list.append({"day": day, "place": city_name})
        
        # Sort by day
        itinerary_list.sort(key=lambda x: x["day"])
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()