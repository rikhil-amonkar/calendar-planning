from z3 import *
import json

def main():
    city_list = ['Edinburgh', 'Budapest', 'Stockholm', 'Warsaw', 'Bucharest', 'Krakow', 'Munich', 'Barcelona', 'Riga', 'Vienna']
    CitySort, city_consts = EnumSort('City', city_list)
    city_dict = {name: const for name, const in zip(city_list, city_consts)}
    rev_city_dict = {const: name for name, const in city_dict.items()}
    
    # Required days for each city
    req_days = {
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
    
    # Direct flight pairs (as provided in the problem)
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
    
    # All positions are distinct (permutation)
    constraints.append(Distinct(positions))
    
    # First city is Edinburgh
    constraints.append(positions[0] == city_dict['Edinburgh'])
    
    # Start and end days for each segment
    for i in range(n):
        c = positions[i]
        # End day = start day + required days - 1
        constraints.append(ends[i] == starts[i] + req_days[c] - 1)
        
        # Fixed start days for specific cities
        if c in fixed_starts:
            constraints.append(starts[i] == fixed_starts[c])
    
    # Start of the first segment is 1
    constraints.append(starts[0] == 1)
    
    # Connection between segments: end of previous is start of next
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
    munich_constraints = []
    for i in range(n):
        c = positions[i]
        munich_constraints.append(
            And(
                c == city_dict['Munich'],
                starts[i] <= 20,
                ends[i] >= 18
            )
        )
    constraints.append(Or(munich_constraints))
    
    # Add all constraints to solver
    s.add(constraints)
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        
        # Evaluate positions, starts, and ends
        pos_vals = [model.evaluate(positions[i]) for i in range(n)]
        start_vals = [model.evaluate(starts[i]).as_long() for i in range(n)]
        end_vals = [model.evaluate(ends[i]).as_long() for i in range(n)]
        
        # Build itinerary for each day (1 to 32)
        itinerary = []
        for day in range(1, 33):
            cities_on_day = []
            for seg in range(n):
                s_day = start_vals[seg]
                e_day = end_vals[seg]
                if s_day <= day <= e_day:
                    city_const = pos_vals[seg]
                    city_name = rev_city_dict[city_const]
                    cities_on_day.append(city_name)
            # Sort for consistent output
            cities_on_day.sort()
            place_str = ", ".join(cities_on_day)
            itinerary.append({"day": day, "place": place_str})
        
        # Output as JSON-formatted dictionary
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()