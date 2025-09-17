from z3 import *
import json

def main():
    # Define cities and their indices
    cities = ['Valencia', 'Oslo', 'Lyon', 'Prague', 'Paris', 'Nice', 'Seville', 'Tallinn', 'Mykonos', 'Lisbon']
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    # Required days for each city
    req_days = [2, 3, 4, 3, 4, 4, 5, 2, 5, 2]
    
    # Direct flights set (as city index pairs)
    direct_flights_pairs = [
        ('Lisbon','Paris'), ('Lyon','Nice'), ('Tallinn','Oslo'), ('Prague','Lyon'), ('Paris','Oslo'),
        ('Lisbon','Seville'), ('Prague','Lisbon'), ('Oslo','Nice'), ('Valencia','Paris'), ('Valencia','Lisbon'),
        ('Paris','Nice'), ('Nice','Mykonos'), ('Paris','Lyon'), ('Valencia','Lyon'), ('Prague','Oslo'),
        ('Prague','Paris'), ('Seville','Paris'), ('Oslo','Lyon'), ('Prague','Valencia'), ('Lisbon','Nice'),
        ('Lisbon','Oslo'), ('Valencia','Seville'), ('Lisbon','Lyon'), ('Paris','Tallinn'), ('Prague','Tallinn')
    ]
    direct_flights_set = set()
    for a, b in direct_flights_pairs:
        i1 = city_index[a]
        i2 = city_index[b]
        direct_flights_set.add((i1, i2))
        direct_flights_set.add((i2, i1))
    
    # Create Z3 solver
    s = Solver()
    
    # Sleep city array for nights 0 to 25
    sleep = IntVector('s', 26)
    for i in range(26):
        s.add(sleep[i] >= 0, sleep[i] < len(cities))
    
    # Constraints for required days per city
    for c_idx in range(len(cities)):
        non_travel = 0
        depart = 0
        arrive = 0
        for i in range(1, 26):
            # Non-travel days: same city on consecutive nights
            non_travel += If(And(sleep[i-1] == c_idx, sleep[i] == c_idx), 1, 0)
            # Departure travel days: leave from city c_idx
            depart += If(And(sleep[i-1] == c_idx, sleep[i] != c_idx), 1, 0)
            # Arrival travel days: arrive to city c_idx
            arrive += If(And(sleep[i-1] != c_idx, sleep[i] == c_idx), 1, 0)
        total_days = non_travel + depart + arrive
        s.add(total_days == req_days[c_idx])
    
    # Meeting constraints
    # Valencia between day 3 and 4: must be in Valencia on day 3 or day 4
    s.add(Or(sleep[2] == city_index['Valencia'], sleep[3] == city_index['Valencia'], sleep[4] == city_index['Valencia']))
    # Oslo between day 13 and 15: must be in Oslo on day 13, 14, or 15
    s.add(Or(sleep[12] == city_index['Oslo'], sleep[13] == city_index['Oslo'], sleep[14] == city_index['Oslo'], sleep[15] == city_index['Oslo']))
    # Seville from day 5 to 9: must be in Seville on at least one of these days
    seville_constraints = []
    for i in range(4, 10):
        seville_constraints.append(sleep[i] == city_index['Seville'])
    s.add(Or(seville_constraints))
    # Mykonos between day 21 and 25: must be in Mykonos on at least one of these days
    mykonos_constraints = []
    for i in range(20, 26):
        mykonos_constraints.append(sleep[i] == city_index['Mykonos'])
    s.add(Or(mykonos_constraints))
    
    # Direct flight constraints
    for i in range(1, 26):
        city_prev = sleep[i-1]
        city_curr = sleep[i]
        # If travel occurs, ensure there is a direct flight
        travel_condition = (city_prev != city_curr)
        allowed_flights = []
        for (c1, c2) in direct_flights_set:
            allowed_flights.append(And(city_prev == c1, city_curr == c2))
        s.add(Implies(travel_condition, Or(allowed_flights)))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        sleep_values = [model.evaluate(sleep[i]).as_long() for i in range(26)]
        
        # Generate itinerary stays
        itinerary = []
        current_city = sleep_values[0]
        start_night = 0
        for night in range(1, 26):
            if sleep_values[night] != current_city:
                end_night = night - 1
                start_day = start_night + 1
                end_day = end_night + 1
                if end_day > 25:
                    end_day = 25
                if start_day == end_day:
                    day_range_str = f"Day {start_day}"
                else:
                    day_range_str = f"Day {start_day}-{end_day}"
                itinerary.append({"day_range": day_range_str, "place": cities[current_city]})
                current_city = sleep_values[night]
                start_night = night
        # Add the last stay
        start_day = start_night + 1
        end_day = 25
        if start_day == end_day:
            day_range_str = f"Day {start_day}"
        else:
            day_range_str = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range_str, "place": cities[current_city]})
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()