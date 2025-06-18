import z3
import json

def main():
    # Define the City enum
    City = z3.DeclareSort('City')
    cities_str = ["Barcelona", "Frankfurt", "Florence", "Stockholm", "Venice", "Stuttgart", "Salzburg"]
    cities_sym = [z3.Const(city, City) for city in cities_str]
    Barcelona, Frankfurt, Florence, Stockholm, Venice, Stuttgart, Salzburg = cities_sym
    
    # Map city symbols to string names
    sym_to_str = {sym: name for sym, name in zip(cities_sym, cities_str)}
    str_to_sym = {name: sym for sym, name in sym_to_str.items()}
    
    # Define the direct flight connections (bidirectional)
    connections = [
        ("Barcelona", "Frankfurt"),
        ("Florence", "Frankfurt"),
        ("Stockholm", "Barcelona"),
        ("Barcelona", "Florence"),
        ("Venice", "Barcelona"),
        ("Stuttgart", "Barcelona"),
        ("Frankfurt", "Salzburg"),
        ("Stockholm", "Frankfurt"),
        ("Stuttgart", "Stockholm"),
        ("Stuttgart", "Frankfurt"),
        ("Venice", "Stuttgart"),
        ("Venice", "Frankfurt")
    ]
    allowed_edges = set()
    for u, v in connections:
        u_sym = str_to_sym[u]
        v_sym = str_to_sym[v]
        allowed_edges.add((u_sym, v_sym))
        allowed_edges.add((v_sym, u_sym))
    
    # Requirements for each city
    requirements = {
        Salzburg: 4,
        Stockholm: 2,
        Venice: 5,
        Frankfurt: 4,
        Florence: 4,
        Barcelona: 2,
        Stuttgart: 3
    }
    
    # Create Z3 solver
    s = z3.Solver()
    
    # Define variables: A[1] to A[19] (start of each day)
    A = [z3.Const(f'A_{i}', City) for i in range(1, 20)]
    # Flight taken on days 1 to 18
    flight_taken = [z3.Bool(f'f_{i}') for i in range(1, 19)]
    
    # Flight constraints for each day
    for i in range(18):
        # If flight taken, ensure direct flight and different cities
        flight_cond = z3.Or([z3.And(A[i] == u, A[i+1] == v) for (u, v) in allowed_edges])
        s.add(z3.If(flight_taken[i], 
                    z3.And(A[i] != A[i+1], flight_cond), 
                    A[i] == A[i+1]))
    
    # Count constraints for each city
    for city in cities_sym:
        total = 0
        for i in range(18):
            # Count start of day
            total += z3.If(A[i] == city, 1, 0)
            # Count arrival on flight days
            total += z3.If(z3.And(flight_taken[i], A[i+1] == city), 1, 0)
        s.add(total == requirements[city])
    
    # Exactly 6 flight days
    s.add(z3.Sum([z3.If(ft, 1, 0) for ft in flight_taken]) == 6)
    
    # Must be in Venice on days 1 to 5
    for i in range(5):
        s.add(z3.Or(A[i] == Venice, 
                    z3.And(flight_taken[i], A[i+1] == Venice)))
    
    # Check and get model
    if s.check() == z3.sat:
        m = s.model()
        # Extract values for A and flight_taken
        A_val = [m.eval(A[i], model_completion=True) for i in range(19)]
        flight_taken_val = [m.eval(flight_taken[i], model_completion=True) for i in range(18)]
        
        # Map to presence sets for each city
        presence = {city: set() for city in cities_sym}
        for i in range(18):
            day = i + 1
            start_city = A_val[i]
            presence[start_city].add(day)
            if z3.is_true(flight_taken_val[i]):
                next_city = A_val[i+1]
                presence[next_city].add(day)
        
        # Generate block records for contiguous days
        records = []
        for city in cities_sym:
            days = sorted(presence[city])
            if not days:
                continue
            intervals = []
            start = days[0]
            end = days[0]
            for d in days[1:]:
                if d == end + 1:
                    end = d
                else:
                    intervals.append((start, end))
                    start = d
                    end = d
            intervals.append((start, end))
            for s_int, e_int in intervals:
                if s_int == e_int:
                    day_range = f"Day {s_int}"
                else:
                    day_range = f"Day {s_int}-{e_int}"
                records.append({
                    "day_range": day_range,
                    "place": sym_to_str[city],
                    "start_day": s_int,
                    "type": "block"
                })
        
        # Generate flight records
        for i in range(18):
            if z3.is_true(flight_taken_val[i]):
                day = i + 1
                dep_city = A_val[i]
                arr_city = A_val[i+1]
                records.append({
                    "day_range": f"Day {day}",
                    "place": sym_to_str[dep_city],
                    "start_day": day,
                    "type": "flight"
                })
                records.append({
                    "day_range": f"Day {day}",
                    "place": sym_to_str[arr_city],
                    "start_day": day,
                    "type": "flight"
                })
        
        # Sort records: by start_day, then flight before block, then by place for tie-breaking
        def record_key(rec):
            type_order = 0 if rec['type'] == 'flight' else 1
            return (rec['start_day'], type_order, rec['place'])
        
        records_sorted = sorted(records, key=record_key)
        # Remove helper keys
        for rec in records_sorted:
            del rec['start_day']
            del rec['type']
        
        # Output as JSON
        result = {"itinerary": records_sorted}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()