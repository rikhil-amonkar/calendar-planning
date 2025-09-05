from z3 import *
import json

def main():
    # List of cities and their required durations
    cities = ["Venice", "Reykjavik", "Munich", "Santorini", "Manchester", "Porto", "Bucharest", "Tallinn", "Valencia", "Vienna"]
    durations = [3, 2, 3, 3, 3, 3, 5, 4, 2, 5]
    
    # Define the direct flights (undirected) as provided.
    # We map each city to its index:
    # 0: Venice, 1: Reykjavik, 2: Munich, 3: Santorini, 4: Manchester,
    # 5: Porto, 6: Bucharest, 7: Tallinn, 8: Valencia, 9: Vienna
    flights = [
        ("Bucharest", "Manchester"),
        ("Munich", "Venice"),
        ("Santorini", "Manchester"),
        ("Vienna", "Reykjavik"),
        ("Venice", "Santorini"),
        ("Munich", "Porto"),
        ("Valencia", "Vienna"),
        ("Manchester", "Vienna"),
        ("Porto", "Vienna"),
        ("Venice", "Manchester"),
        ("Santorini", "Vienna"),
        ("Munich", "Manchester"),
        ("Munich", "Reykjavik"),
        ("Bucharest", "Valencia"),
        ("Venice", "Vienna"),
        ("Bucharest", "Vienna"),
        ("Porto", "Manchester"),
        ("Munich", "Vienna"),
        ("Valencia", "Porto"),
        ("Munich", "Bucharest"),
        ("Tallinn", "Munich"),
        ("Santorini", "Bucharest"),
        ("Munich", "Valencia")
    ]
    city_to_index = { name: idx for idx, name in enumerate(cities) }
    
    # Build allowed transition pairs (both directions)
    allowed_pairs = set()
    for (a, b) in flights:
        i = city_to_index[a]
        j = city_to_index[b]
        allowed_pairs.add((i, j))
        allowed_pairs.add((j, i))
    allowed_transitions = list(allowed_pairs)
    
    s = Solver()
    
    # We will decide on an ordering of the 10 cities. 
    # order[k] will be the index into 'cities' for position k in the itinerary.
    order = [Int(f"order_{k}") for k in range(10)]
    for k in range(10):
        s.add(order[k] >= 0, order[k] < 10)
    s.add(Distinct(order))
    
    # The itinerary segments start on days given by start_vars.
    start_vars = [Int(f"start_{k}") for k in range(10)]
    for k in range(10):
        s.add(start_vars[k] >= 1, start_vars[k] <= 24)
    
    # The first segment starts on day 1.
    s.add(start_vars[0] == 1)
    
    # Helper: for a given itinerary position, return the duration of the city there.
    # This uses a piecewise expression based on the value of order[k].
    def duration_expr(k):
        return Sum([If(order[k] == i, durations[i], 0) for i in range(10)])
    
    # Link the segments via flight transitions.
    # If you depart from a city, then the flight is taken on the last day of that city,
    # and the next city is entered on the same day.
    for k in range(9):
        s.add(start_vars[k+1] == start_vars[k] + duration_expr(k) - 1)
    # The last segment must end on day 24.
    s.add(start_vars[9] + duration_expr(9) - 1 == 24)
    
    # Special constraints due to event requirements:
    # Munich (index 2) must be visited for 3 days and the annual show in Munich is from day 4 to day 6.
    # Since a 3-day visit means if the visit starts on day X then the days are X, X+1, X+2,
    # the only valid way for Munich to include days 4,5,6 is to have its start day equal 4.
    for k in range(10):
        s.add(Implies(order[k] == 2, start_vars[k] == 4))
    
    # Santorini (index 3) must be visited for 3 days and you visit relatives between day 8 and 10.
    # To overlap with [8,10], the Santorini segment must satisfy: start <= 10 and start+2 >= 8,
    # i.e. start ∈ [6, 10].
    for k in range(10):
        s.add(Implies(order[k] == 3, And(start_vars[k] >= 6, start_vars[k] <= 10)))
    
    # Valencia (index 8) is visited for 2 days, and you attend a workshop there between day 14 and 15.
    # So the Valencia segment [start, start+1] must overlap that window.
    # This is ensured if start <= 15 and start+1 >= 14, i.e. start ∈ [13,15].
    for k in range(10):
        s.add(Implies(order[k] == 8, And(start_vars[k] >= 13, start_vars[k] <= 15)))
    
    # Flight connectivity constraints: For each consecutive pair in the itinerary,
    # there must be a direct flight between the two cities.
    for k in range(9):
        transition_allowed = []
        for (a, b) in allowed_transitions:
            transition_allowed.append(And(order[k] == a, order[k+1] == b))
        s.add(Or(transition_allowed))
    
    # Solve the SMT constraints.
    if s.check() == sat:
        m = s.model()
        itinerary = []
        # The itinerary is defined by the order positions 0 through 9.
        for k in range(10):
            city_index = m.evaluate(order[k]).as_long()
            start_day = m.evaluate(start_vars[k]).as_long()
            seg_duration = durations[city_index]
            end_day = start_day + seg_duration - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": cities[city_index]
            })
        result = {"itinerary": itinerary}
    else:
        result = {"error": "No itinerary found"}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()