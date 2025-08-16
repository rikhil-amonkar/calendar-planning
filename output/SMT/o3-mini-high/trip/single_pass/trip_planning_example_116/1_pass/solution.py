from z3 import *

def main():
    num_days = 18  # days 1..18 (we use 0-indexing for variables: day i corresponds to i+1)
    # We use the following integer encoding:
    #   0 : Split
    #   1 : London
    #   2 : Santorini
    city_names = {0: "Split", 1: "London", 2: "Santorini"}
    
    # Create an array x[0..17] for the city assignment on each day.
    city_vars = [Int("x_%d" % i) for i in range(num_days)]
    
    # Create a Boolean array f[0..17] where f[i] (for i>=1) is true if a flight is taken on day i+1.
    # (We force f[0] = False because there is no “flight day” on day 1.)
    flight_vars = [Bool("f_%d" % i) for i in range(num_days)]
    
    s = Solver()
    
    # Domain: each x[i] must be one of the 3 cities.
    for i in range(num_days):
        s.add(Or(city_vars[i] == 0, city_vars[i] == 1, city_vars[i] == 2))
    
    # Day 1: no flight.
    s.add(flight_vars[0] == False)
    
    # For days 2...18 (i=1..17), if no flight then carry over same city;
    # if there is a flight then the day counts for both the previous and the new city.
    # Also, if f[i] is true then the flight must be direct:
    # Allowed direct flights are:
    #     London <-> Santorini and Split <-> London.
    for i in range(1, num_days):
        # If no flight this day, city remains the same.
        s.add(Implies(Not(flight_vars[i]), city_vars[i] == city_vars[i-1]))
        # If there is a flight this day, then the pair (x[i-1], x[i]) must be allowed.
        allowed_flights = Or(
            And(city_vars[i-1] == 1, city_vars[i] == 2),  # London -> Santorini
            And(city_vars[i-1] == 2, city_vars[i] == 1),  # Santorini -> London
            And(city_vars[i-1] == 1, city_vars[i] == 0),  # London -> Split
            And(city_vars[i-1] == 0, city_vars[i] == 1)   # Split -> London
        )
        s.add(Implies(flight_vars[i], allowed_flights))
    
    # There must be exactly 2 flight days.
    s.add(Sum([If(f, 1, 0) for f in flight_vars]) == 2)
    
    # Conference days: Day 12 and day 18 (indices 11 and 17) must include Santorini.
    # We enforce that the city variable for those days is Santorini (2).
    s.add(city_vars[11] == 2)  # day 12
    s.add(city_vars[17] == 2)  # day 18
    
    # Define a helper function to compute the “count” of days in a given city.
    # On day 1 (i==0): you get 1 point if city_vars[0] equals that city.
    # For day i (i>=1): if f[i] is true then add 1 for x[i-1] and 1 for x[i];
    # otherwise add 1 for x[i] (since it’s a full day staying in the same place).
    def day_count(city_val):
        count_expr = If(city_vars[0] == city_val, 1, 0)
        for i in range(1, num_days):
            count_expr = count_expr + If(flight_vars[i],
                                         If(city_vars[i-1] == city_val, 1, 0) + If(city_vars[i] == city_val, 1, 0),
                                         If(city_vars[i] == city_val, 1, 0))
        return count_expr
    
    # Add the overall days constraints:
    # Split (0) for 6 days, London (1) for 7 days, Santorini (2) for 7 days.
    s.add(day_count(0) == 6)
    s.add(day_count(1) == 7)
    s.add(day_count(2) == 7)
    
    # Check and display a solution.
    if s.check() == sat:
        m = s.model()
        itinerary = []
        # We produce a list of day mappings.
        # For day 1 (index 0) there is a single city.
        # For subsequent days (i>=1): if a flight occurs (f[i]==True),
        # then we output both the previous day’s city and the current city.
        for i in range(num_days):
            if i == 0:
                day_place = city_names[m[city_vars[i]].as_long()]
            else:
                if m.evaluate(flight_vars[i]):
                    # Flight day: include both the city from the previous day and the current day.
                    prev_city = city_names[m[city_vars[i-1]].as_long()]
                    curr_city = city_names[m[city_vars[i]].as_long()]
                    day_place = [prev_city, curr_city]
                else:
                    day_place = city_names[m[city_vars[i]].as_long()]
            itinerary.append({"day": i+1, "place": day_place})
        
        # Output as JSON.
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()