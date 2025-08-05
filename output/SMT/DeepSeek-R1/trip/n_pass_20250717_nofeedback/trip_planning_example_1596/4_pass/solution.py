from z3 import *
import json

def main():
    city_list = ['Edinburgh', 'Budapest', 'Stockholm', 'Warsaw', 'Bucharest', 'Krakow', 'Munich', 'Barcelona', 'Riga', 'Vienna']
    CitySort, city_consts = EnumSort('City', city_list)
    city_dict = {name: const for name, const in zip(city_list, city_consts)}
    rev_city_dict = {const: name for name, const in city_dict.items()}
    
    # Required days for each city (as Z3 function)
    req_days_z3 = Function('req_days', CitySort, IntSort())
    req_days_map = {
        city_dict['Edinburgh']: 5,
        city_dict['Budapest']: 5,
        city_dict['Stockholm']: 2,
        city_dict['Warsaw']: 5,
        city_dict['Bucharest']: 2,
        city_dict['Krakow']: 4,
        city_dict['Munich']: 3,
        city_dict['Barcelona']: 5,
        city_dict['Riga']: 5,
        city_dict['Vienna']: 5
    }
    
    # Fixed start days for specific cities
    fixed_starts = {
        city_dict['Edinburgh']: 1,
        city_dict['Budapest']: 9,
        city_dict['Stockholm']: 17,
        city_dict['Warsaw']: 25
    }
    
    # Direct flight pairs
    flight_pairs_str = [
        "Budapest and Munich",
        "Bucharest and Riga",
        "Munich and Krakow",
        "Munich and Warsaw",
        "Munich and Bucharest",
        "Edinburgh and Stockholm",
        "Barcelona and Warsaw",
        "Edinburgh and Krakow",
        "Barcelona and Munich",
        "Stockholm and Krakow",
        "Budapest and Vienna",
        "Barcelona and Stockholm",
        "Stockholm and Munich",
        "Edinburgh and Budapest",
        "Barcelona and Riga",
        "Edinburgh and Barcelona",
        "Vienna and Riga",
        "Barcelona and Budapest",
        "Bucharest and Warsaw",
        "Edinburgh and Riga",
        "Vienna and Stockholm",
        "Warsaw and Krakow",
        "Barcelona and Krakow",
        "from Riga to Munich",
        "Vienna and Bucharest",
        "Budapest and Warsaw",
        "Vienna and Warsaw",
        "Barcelona and Vienna",
        "Budapest and Bucharest",
        "Vienna and Munich",
        "Riga and Warsaw",
        "Stockholm and Riga",
        "Stockholm and Warsaw"
    ]
    
    # Normalize and extract city pairs
    normalized_flight_str = [s.replace("from ", "").replace(" to ", " and ") for s in flight_pairs_str]
    flight_pairs_clean = []
    for s in normalized_flight_str:
        parts = s.split(" and ")
        if len(parts) < 2:
            continue
        city1 = parts[0].strip()
        city2 = parts[1].strip()
        flight_pairs_clean.append((city1, city2))
    
    # Create set of flight pairs (both directions)
    flight_pairs = set()
    for (a, b) in flight_pairs_clean:
        a_const = city_dict[a]
        b_const = city_dict[b]
        flight_pairs.add((a_const, b_const))
        flight_pairs.add((b_const, a_const))
    
    # Create Z3 solver and variables
    s = Solver()
    n = 10  # number of cities
    
    # Position variables: sequence of cities
    positions = [Const('pos_%d' % i, CitySort) for i in range(n)]
    
    # Start and end days for each segment
    starts = [Int('start_%d' % i) for i in range(n)]
    ends = [Int('end_%d' % i) for i in range(n)]
    
    # Constraints
    constraints = []
    
    # Define required days via Z3 function
    for city_const, days in req_days_map.items():
        constraints.append(req_days_z3(city_const) == days)
    
    # All positions are distinct
    constraints.append(Distinct(positions))
    
    # First city is Edinburgh
    constraints.append(positions[0] == city_dict['Edinburgh'])
    
    # Start and end days for each segment
    for i in range(n):
        c = positions[i]
        # End day = start day + required days - 1
        constraints.append(ends[i] == starts[i] + req_days_z3(c) - 1)
        
        # Fixed start days using implications
        for city_const, fixed_day in fixed_starts.items():
            constraints.append(Implies(c == city_const, starts[i] == fixed_day))
    
    # Start of first segment is 1
    constraints.append(starts[0] == 1)
    
    # Connection between segments: next segment starts on the same day the previous segment ends (flight day shared)
    for i in range(1, n):
        constraints.append(starts[i] == ends[i-1])
    
    # Last segment ends at day 32
    constraints.append(ends[n-1] == 32)
    
    # Flight constraints: consecutive cities must have a direct flight
    for i in range(n-1):
        c1 = positions[i]
        c2 = positions[i+1]
        constraints.append(Or([And(c1 == a, c2 == b) for (a, b) in flight_pairs]))
    
    # Munich must include at least one day between 18 and 20
    munich_constraint = Or([
        And(
            positions[i] == city_dict['Munich'],
            starts[i] <= 20,
            ends[i] >= 18
        ) for i in range(n)
    ])
    constraints.append(munich_constraint)
    
    # Add all constraints
    s.add(constraints)
    
    # Solve and output itinerary
    if s.check() == sat:
        model = s.model()
        pos_vals = [model.evaluate(positions[i]) for i in range(n)]
        start_vals = [model.evaluate(starts[i]).as_long() for i in range(n)]
        end_vals = [model.evaluate(ends[i]).as_long() for i in range(n)]
        
        itinerary = []
        for day in range(1, 33):
            cities = []
            for seg in range(n):
                if start_vals[seg] <= day <= end_vals[seg]:
                    city_name = rev_city_dict[pos_vals[seg]]
                    cities.append(city_name)
            cities.sort()
            itinerary.append({"day": day, "place": ", ".join(cities)})
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()