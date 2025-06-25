from z3 import *

def main():
    # Define city names and their integer mappings
    cities = [
        'Paris',        # 0
        'Vienna',       # 1
        'Barcelona',    # 2
        'Edinburgh',    # 3
        'Krakow',       # 4
        'Riga',         # 5
        'Hamburg',      # 6
        'Stockholm'     # 7
    ]
    
    # Direct flight connections as strings
    connections = [
        "Hamburg and Stockholm", "Vienna and Stockholm", "Paris and Edinburgh", "Riga and Barcelona", "Paris and Riga",
        "Krakow and Barcelona", "Edinburgh and Stockholm", "Paris and Krakow", "Krakow and Stockholm", "Riga and Edinburgh",
        "Barcelona and Stockholm", "Paris and Stockholm", "Krakow and Edinburgh", "Vienna and Hamburg", "Paris and Hamburg",
        "Riga and Stockholm", "Hamburg and Barcelona", "Vienna and Barcelona", "Krakow and Vienna", "from Riga to Hamburg"
    ]
    
    # Build set of flight pairs as (min_id, max_id)
    flight_pairs = set()
    for conn in connections:
        if " and " in conn:
            a, b = conn.split(" and ")
            a_id = cities.index(a)
            b_id = cities.index(b)
            flight_pairs.add((min(a_id, b_id), max(a_id, b_id)))
        elif " to " in conn:
            parts = conn.split()
            a = parts[1]
            b = parts[3]
            a_id = cities.index(a)
            b_id = cities.index(b)
            flight_pairs.add((min(a_id, b_id), max(a_id, b_id)))
    
    flight_pairs = list(flight_pairs)  # Convert to list for iteration in constraints

    # Initialize Z3 solver
    s = Solver()
    
    # Define variables for the end days of the first 6 segments (city1 to city6)
    e2 = Int('e2')
    e3 = Int('e3')
    e4 = Int('e4')
    e5 = Int('e5')
    e6 = Int('e6')
    
    # Define city variables for positions 1 to 6 in the sequence (city1 to city6)
    city1 = Int('city1')
    city2 = Int('city2')
    city3 = Int('city3')
    city4 = Int('city4')
    city5 = Int('city5')
    city6 = Int('city6')
    
    # Entire sequence of cities (0: Paris, 7: Stockholm)
    seq = [0, city1, city2, city3, city4, city5, city6, 7]
    
    # Constraints for end days: 2 <= e2 <= e3 <= e4 <= e5 <= e6 <= 15
    s.add(e2 >= 2, e2 <= 15)
    s.add(e3 >= e2, e3 <= 15)
    s.add(e4 >= e3, e4 <= 15)
    s.add(e5 >= e4, e5 <= 15)
    s.add(e6 >= e5, e6 <= 15)
    
    # City variables must be between 1 and 6 (inclusive) and distinct
    s.add(city1 >= 1, city1 <= 6)
    s.add(city2 >= 1, city2 <= 6)
    s.add(city3 >= 1, city3 <= 6)
    s.add(city4 >= 1, city4 <= 6)
    s.add(city5 >= 1, city5 <= 6)
    s.add(city6 >= 1, city6 <= 6)
    s.add(Distinct(city1, city2, city3, city4, city5, city6))
    
    # Length of stay for each city in the sequence (positions 1 to 6)
    len1 = e2 - 1  # For city1 (starts at day2, ends at e2)
    len2 = e3 - e2 + 1  # For city2
    len3 = e4 - e3 + 1  # For city3
    len4 = e5 - e4 + 1  # For city4
    len5 = e6 - e5 + 1  # For city5
    len6 = 16 - e6  # For city6 (ends at day15)
    
    # Length constraints for each city based on its type
    for i, len_i in enumerate([len1, len2, len3, len4, len5, len6], 1):
        s.add(Or(
            And(seq[i] == 1, len_i == 4),  # Vienna
            And(seq[i] == 2, len_i == 2),  # Barcelona
            And(seq[i] == 3, len_i == 4),  # Edinburgh
            And(seq[i] == 4, len_i == 3),  # Krakow
            And(seq[i] == 5, len_i == 4),  # Riga
            And(seq[i] == 6, len_i == 2)   # Hamburg
        ))
    
    # Hamburg must be in positions 2 to 5 (third to sixth city) with specific day constraints
    s.add(Or(
        And(seq[2] == 6, e2 == 10, e3 == 11),  # Hamburg at position2
        And(seq[3] == 6, e3 == 10, e4 == 11),  # Hamburg at position3
        And(seq[4] == 6, e4 == 10, e5 == 11),  # Hamburg at position4
        And(seq[5] == 6, e5 == 10, e6 == 11)   # Hamburg at position5
    ))
    s.add(Or(seq[2] == 6, seq[3] == 6, seq[4] == 6, seq[5] == 6))  # Hamburg must be in one of these positions
    
    # Edinburgh constraints: if in positions 1 to 5, then the end day must be >= 12
    s.add(Implies(seq[1] == 3, e2 >= 12))  # Position1 (second city)
    s.add(Implies(seq[2] == 3, e3 >= 12))  # Position2
    s.add(Implies(seq[3] == 3, e4 >= 12))  # Position3
    s.add(Implies(seq[4] == 3, e5 >= 12))  # Position4
    s.add(Implies(seq[5] == 3, e6 >= 12))  # Position5
    
    # Direct flight constraints between consecutive cities
    for i in range(7):
        a = seq[i]
        b = seq[i+1]
        min_ab = If(a <= b, a, b)
        max_ab = If(a <= b, b, a)
        constraints = []
        for pair in flight_pairs:
            constraints.append(And(min_ab == pair[0], max_ab == pair[1]))
        s.add(Or(constraints))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Retrieve values for end days and city assignments
        e2_val = m[e2].as_long()
        e3_val = m[e3].as_long()
        e4_val = m[e4].as_long()
        e5_val = m[e5].as_long()
        e6_val = m[e6].as_long()
        
        city1_val = m[city1].as_long()
        city2_val = m[city2].as_long()
        city3_val = m[city3].as_long()
        city4_val = m[city4].as_long()
        city5_val = m[city5].as_long()
        city6_val = m[city6].as_long()
        
        # Build the entire sequence
        full_seq = [
            0,  # Paris
            city1_val,
            city2_val,
            city3_val,
            city4_val,
            city5_val,
            city6_val,
            7   # Stockholm
        ]
        # Map to city names
        seq_names = [cities[idx] for idx in full_seq]
        
        # Start and end days for each city in the sequence
        start_days = [1, 2, e2_val, e3_val, e4_val, e5_val, e6_val, 15]
        end_days = [2, e2_val, e3_val, e4_val, e5_val, e6_val, 15, 16]
        
        # Generate itinerary
        itinerary = []
        for i in range(8):
            start = start_days[i]
            end = end_days[i]
            place = seq_names[i]
            
            # Add the continuous stay block
            itinerary.append({
                "day_range": f"Day {start}-{end}",
                "place": place
            })
            
            # If not the last city, add flight day records
            if i < 7:
                next_place = seq_names[i+1]
                itinerary.append({
                    "day_range": f"Day {end}",
                    "place": place
                })
                itinerary.append({
                    "day_range": f"Day {end}",
                    "place": next_place
                })
        
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()