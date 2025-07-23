from z3 import *

def main():
    CitySort, city_consts = EnumSort('City', [
        'Edinburgh',
        'Budapest',
        'Stockholm',
        'Warsaw',
        'Bucharest',
        'Krakow',
        'Munich',
        'Barcelona',
        'Riga',
        'Vienna'
    ])
    
    # Map city constants to their string names
    city_names = {
        city_consts.Edinburgh: "Edinburgh",
        city_consts.Budapest: "Budapest",
        city_consts.Stockholm: "Stockholm",
        city_consts.Warsaw: "Warsaw",
        city_consts.Bucharest: "Bucharest",
        city_consts.Krakow: "Krakow",
        city_consts.Munich: "Munich",
        city_consts.Barcelona: "Barcelona",
        city_consts.Riga: "Riga",
        city_consts.Vienna: "Vienna"
    }
    
    # Required days for each city
    req_days = {
        city_consts.Edinburgh: 5,
        city_consts.Budapest: 5,
        city_consts.Stockholm: 2,
        city_consts.Warsaw: 5,
        city_consts.Bucharest: 2,
        city_consts.Krakow: 4,
        city_consts.Munich: 3,
        city_consts.Barcelona: 5,
        city_consts.Riga: 5,
        city_consts.Vienna: 5
    }
    
    # Fixed start days for specific cities
    fixed_starts = {
        city_consts.Edinburgh: 1,
        city_consts.Budapest: 9,
        city_consts.Stockholm: 17,
        city_consts.Warsaw: 25
    }
    
    # Direct flight pairs (as a set of tuples)
    flight_pairs_str = [
        ("Budapest", "Munich"),
        ("Bucharest", "Riga"),
        ("Munich", "Krakow"),
        ("Munich", "Warsaw"),
        ("Munich", "Bucharest"),
        ("Edinburgh", "Stockholm"),
        ("Barcelona", "Warsaw"),
        ("Edinburgh", "Krakow"),
        ("Barcelona", "Munich"),
        ("Stockholm", "Krakow"),
        ("Budapest", "Vienna"),
        ("Barcelona", "Stockholm"),
        ("Stockholm", "Munich"),
        ("Edinburgh", "Budapest"),
        ("Barcelona", "Riga"),
        ("Edinburgh", "Barcelona"),
        ("Vienna", "Riga"),
        ("Barcelona", "Budapest"),
        ("Bucharest", "Warsaw"),
        ("Edinburgh", "Riga"),
        ("Vienna", "Stockholm"),
        ("Warsaw", "Krakow"),
        ("Barcelona", "Krakow"),
        ("Riga", "Munich"),
        ("Vienna", "Bucharest"),
        ("Budapest", "Warsaw"),
        ("Vienna", "Warsaw"),
        ("Barcelona", "Vienna"),
        ("Budapest", "Bucharest"),
        ("Vienna", "Munich"),
        ("Riga", "Warsaw"),
        ("Stockholm", "Riga"),
        ("Stockholm", "Warsaw")
    ]
    
    # Convert string pairs to city constants
    flight_pairs = set()
    for a, b in flight_pairs_str:
        a_const = getattr(city_consts, a)
        b_const = getattr(city_consts, b)
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
    constraints.append(positions[0] == city_consts.Edinburgh)
    
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
        # Check if (c1, c2) is in flight_pairs
        pair_constraints = [And(c1 == a, c2 == b) for (a, b) in flight_pairs]
        constraints.append(Or(pair_constraints))
    
    # Munich must include at least one day between 18 and 20
    munich_constraints = []
    for i in range(n):
        c = positions[i]
        munich_constraints.append(
            And(
                c == city_consts.Munich,
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
                    city_name = city_names[city_const]
                    cities_on_day.append(city_name)
            # Sort for consistent output (optional)
            cities_on_day.sort()
            place_str = ", ".join(cities_on_day)
            itinerary.append({"day": day, "place": place_str})
        
        # Output as JSON-formatted dictionary
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()