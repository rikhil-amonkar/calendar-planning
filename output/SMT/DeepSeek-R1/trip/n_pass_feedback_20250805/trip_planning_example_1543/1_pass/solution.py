from z3 import *
import json

def main():
    # Fixed cities with their fixed schedules
    fixed_cities = {
        "Prague": (1, 3),
        "London": (3, 5),
        "Lisbon": (5, 9),
        "Porto": (16, 20),
        "Warsaw": (20, 23)
    }
    
    # Free cities with their required days
    free_cities = {
        "Dublin": 3,
        "Athens": 3,
        "Vilnius": 4,
        "Seville": 2,
        "Dubrovnik": 3
    }
    free_city_names = list(free_cities.keys())
    
    # Direct flight graph (undirected)
    edges = [
        ("Warsaw", "Vilnius"),
        ("Prague", "Athens"),
        ("London", "Lisbon"),
        ("Lisbon", "Porto"),
        ("Prague", "Lisbon"),
        ("London", "Dublin"),
        ("Athens", "Vilnius"),
        ("Athens", "Dublin"),
        ("Prague", "London"),
        ("London", "Warsaw"),
        ("Dublin", "Seville"),
        ("Seville", "Porto"),
        ("Lisbon", "Athens"),
        ("Dublin", "Porto"),
        ("Athens", "Warsaw"),
        ("Lisbon", "Warsaw"),
        ("Porto", "Warsaw"),
        ("Prague", "Warsaw"),
        ("Prague", "Dublin"),
        ("Athens", "Dubrovnik"),
        ("Lisbon", "Dublin"),
        ("Dubrovnik", "Dublin"),
        ("Lisbon", "Seville"),
        ("London", "Athens")
    ]
    graph = {}
    for a, b in edges:
        if a not in graph:
            graph[a] = []
        if b not in graph:
            graph[b] = []
        graph[a].append(b)
        graph[b].append(a)
    
    s = Solver()
    
    # Assign each free city to a group: 0 for gap1 (after Lisbon until Porto), 1 for gap2 (after Warsaw until day26)
    group = {}
    for city in free_city_names:
        group[city] = Int(f'group_{city}')
        s.add(Or(group[city] == 0, group[city] == 1))
    
    # Order within the group: non-negative integer, but we will enforce contiguous ordering per group
    order = {}
    for city in free_city_names:
        order[city] = Int(f'order_{city}')
        s.add(order[city] >= 0)
    
    # We have two groups. For each group, we need to know the cities in it and their order.
    # Also, for each group, we need the sequence of cities to be such that consecutive ones are connected by a direct flight.
    # Additionally, the first city in gap1 must be connected to Lisbon, and the last in gap1 to Porto.
    # For gap2, the first city must be connected to Warsaw.
    
    # For each group, we enforce that the orders are contiguous and start from 0.
    # First, we count the number of cities in each group.
    group0_count = Int('group0_count')
    group1_count = Int('group1_count')
    s.add(group0_count == Sum([If(group[city] == 0, 1, 0) for city in free_city_names]))
    s.add(group1_count == Sum([If(group[city] == 1, 1, 0) for city in free_city_names]))
    s.add(group0_count + group1_count == 5)
    
    # For gap1 (group0), the orders must be from 0 to group0_count-1.
    for city in free_city_names:
        s.add(Implies(group[city] == 0, And(order[city] >= 0, order[city] < group0_count)))
        s.add(Implies(group[city] == 1, And(order[city] >= 0, order[city] < group1_count)))
    
    # Enforce that within each group, the orders are distinct.
    for i in range(len(free_city_names)):
        for j in range(i+1, len(free_city_names)):
            c1 = free_city_names[i]
            c2 = free_city_names[j]
            s.add(Implies(And(group[c1] == group[c2]), order[c1] != order[c2]))
    
    # Now, we define the start and end days for each free city.
    start_day = {}
    end_day = {}
    for city in free_city_names:
        start_day[city] = Int(f'start_{city}')
        end_day[city] = Int(f'end_{city}')
        s.add(end_day[city] == start_day[city] + free_cities[city] - 1)
    
    # For gap1: the first city starts at day 10, the last city ends at day 15.
    # For gap2: the first city starts at day 24, the last city ends at day 26.
    s.add(group0_count >= 1)  # At least one city in gap1 to cover the days
    s.add(group1_count >= 1)  # At least one city in gap2
    
    # Gap1: 
    #   The city with order 0 in group0 must have start_day = 10.
    #   The city with order = group0_count-1 in group0 must have end_day = 15.
    for city in free_city_names:
        s.add(Implies(And(group[city] == 0, order[city] == 0), start_day[city] == 10))
        s.add(Implies(And(group[city] == 0, order[city] == group0_count-1), end_day[city] == 15))
    
    # For consecutive cities in group0: the end_day of the city with order i must be one less than the start_day of the city with order i+1? 
    # Actually, we fly on the same day: so the next city starts on the same day the previous ends.
    for i in range(len(free_city_names)):
        for j in range(len(free_city_names)):
            if i == j:
                continue
            c1 = free_city_names[i]
            c2 = free_city_names[j]
            s.add(Implies(And(group[c1] == 0, group[c2] == 0, order[c2] == order[c1] + 1),
                       start_day[c2] == end_day[c1]))
    
    # Gap2:
    for city in free_city_names:
        s.add(Implies(And(group[city] == 1, order[city] == 0), start_day[city] == 24))
        s.add(Implies(And(group[city] == 1, order[city] == group1_count-1), end_day[city] == 26))
    
    for i in range(len(free_city_names)):
        for j in range(len(free_city_names)):
            if i == j:
                continue
            c1 = free_city_names[i]
            c2 = free_city_names[j]
            s.add(Implies(And(group[c1] == 1, group[c2] == 1, order[c2] == order[c1] + 1),
                       start_day[c2] == end_day[c1]))
    
    # Flight connection constraints:
    # For gap1 group0:
    #   The first city (order0) must be connected to Lisbon.
    #   The last city (order = group0_count-1) must be connected to Porto.
    #   For consecutive cities in group0: consecutive in order must be connected.
    for city in free_city_names:
        # First in gap1
        s.add(Implies(And(group[city] == 0, order[city] == 0), 
                       Or( 
                           And(city == "Dublin", "Lisbon" in graph["Dublin"]),
                           And(city == "Athens", "Lisbon" in graph["Athens"]),
                           And(city == "Vilnius", "Lisbon" in graph["Vilnius"]),
                           And(city == "Seville", "Lisbon" in graph["Seville"]),
                           And(city == "Dubrovnik", "Lisbon" in graph["Dubrovnik"])
                       )))
        # Last in gap1
        s.add(Implies(And(group[city] == 0, order[city] == group0_count-1),
                       Or(
                           And(city == "Dublin", "Porto" in graph["Dublin"]),
                           And(city == "Athens", "Porto" in graph["Athens"]),
                           And(city == "Vilnius", "Porto" in graph["Vilnius"]),
                           And(city == "Seville", "Porto" in graph["Seville"]),
                           And(city == "Dubrovnik", "Porto" in graph["Dubrovnik"])
                       )))
        # First in gap2
        s.add(Implies(And(group[city] == 1, order[city] == 0),
                       Or(
                           And(city == "Dublin", "Warsaw" in graph["Dublin"]),
                           And(city == "Athens", "Warsaw" in graph["Athens"]),
                           And(city == "Vilnius", "Warsaw" in graph["Vilnius"]),
                           And(city == "Seville", "Warsaw" in graph["Seville"]),
                           And(city == "Dubrovnik", "Warsaw" in graph["Dubrovnik"])
                       )))
    
    # Consecutive within gap1 and gap2
    for i in range(len(free_city_names)):
        for j in range(len(free_city_names)):
            if i == j:
                continue
            c1 = free_city_names[i]
            c2 = free_city_names[j]
            # In the same group and consecutive order
            cond = And(group[c1] == group[c2], order[c2] == order[c1] + 1)
            # They must have a direct flight
            edge_cond = Or(
                And(c1 == "Dublin", c2 == "Athens", "Dublin" in graph.get("Athens", [])),
                And(c1 == "Dublin", c2 == "Vilnius", "Dublin" in graph.get("Vilnius", [])),
                And(c1 == "Dublin", c2 == "Seville", "Dublin" in graph.get("Seville", [])),
                And(c1 == "Dublin", c2 == "Dubrovnik", "Dublin" in graph.get("Dubrovnik", [])),
                And(c1 == "Athens", c2 == "Dublin", "Athens" in graph.get("Dublin", [])),
                And(c1 == "Athens", c2 == "Vilnius", "Athens" in graph.get("Vilnius", [])),
                And(c1 == "Athens", c2 == "Seville", "Athens" in graph.get("Seville", [])),
                And(c1 == "Athens", c2 == "Dubrovnik", "Athens" in graph.get("Dubrovnik", [])),
                And(c1 == "Vilnius", c2 == "Dublin", "Vilnius" in graph.get("Dublin", [])),
                And(c1 == "Vilnius", c2 == "Athens", "Vilnius" in graph.get("Athens", [])),
                And(c1 == "Vilnius", c2 == "Seville", "Vilnius" in graph.get("Seville", [])),
                And(c1 == "Vilnius", c2 == "Dubrovnik", "Vilnius" in graph.get("Dubrovnik", [])),
                And(c1 == "Seville", c2 == "Dublin", "Seville" in graph.get("Dublin", [])),
                And(c1 == "Seville", c2 == "Athens", "Seville" in graph.get("Athens", [])),
                And(c1 == "Seville", c2 == "Vilnius", "Seville" in graph.get("Vilnius", [])),
                And(c1 == "Seville", c2 == "Dubrovnik", "Seville" in graph.get("Dubrovnik", [])),
                And(c1 == "Dubrovnik", c2 == "Dublin", "Dubrovnik" in graph.get("Dublin", [])),
                And(c1 == "Dubrovnik", c2 == "Athens", "Dubrovnik" in graph.get("Athens", [])),
                And(c1 == "Dubrovnik", c2 == "Vilnius", "Dubrovnik" in graph.get("Vilnius", [])),
                And(c1 == "Dubrovnik", c2 == "Seville", "Dubrovnik" in graph.get("Seville", []))
            )
            s.add(Implies(cond, edge_cond))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        
        # Collect group and order assignments
        assignment = {}
        for city in free_city_names:
            g = m[group[city]].as_long()
            o = m[order[city]].as_long()
            assignment[city] = (g, o)
        
        # Build the entire itinerary
        itinerary = []
        
        # Fixed part: days 1 to 23
        for day in range(1, 10):
            if day <= 3:
                itinerary.append(("Prague", day))
            elif day <= 5:
                itinerary.append(("London", day))
            else:
                itinerary.append(("Lisbon", day))
        
        # Gap1: days 10 to 15
        # Get the cities in group0 and sort by order
        group0_cities = []
        for city in free_city_names:
            g, o = assignment[city]
            if g == 0:
                group0_cities.append((o, city))
        group0_cities.sort(key=lambda x: x[0])
        group0_cities = [x[1] for x in group0_cities]
        
        current_day = 10
        for city in group0_cities:
            days_needed = free_cities[city]
            for i in range(days_needed):
                itinerary.append((city, current_day + i))
            current_day += days_needed - 1  # Because the last day is shared with the next city
        
        # Porto: days 16 to 20
        for day in range(16, 21):
            itinerary.append(("Porto", day))
        
        # Warsaw: days 20 to 23
        for day in range(20, 24):
            itinerary.append(("Warsaw", day))
        
        # Gap2: days 24 to 26
        group1_cities = []
        for city in free_city_names:
            g, o = assignment[city]
            if g == 1:
                group1_cities.append((o, city))
        group1_cities.sort(key=lambda x: x[0])
        group1_cities = [x[1] for x in group1_cities]
        
        current_day = 24
        for city in group1_cities:
            days_needed = free_cities[city]
            for i in range(days_needed):
                itinerary.append((city, current_day + i))
            current_day += days_needed - 1
        
        # Create the day-place mappings
        day_place = {}
        for city, day in itinerary:
            if day not in day_place:
                day_place[day] = []
            day_place[day].append(city)
        
        # For days with multiple cities, we choose one arbitrarily? 
        # But the problem says that on a flight day, you are in both cities. 
        # However, the output should be a list of day-place mappings? How to represent a day with two cities?
        # The problem says: "Your output should be a JSON-formatted dictionary with an 'itinerary' key containing a list of day-place mappings."
        # And the example: 
        #   If you stay in Venice from Day 1-3 and fly to Vienna on Day 3, then Venice: Day 1-3, Vienna: Day 3-6.
        #   The flight day (Day 3) is counted for both.
        # But in the JSON output, how do we represent day3? The problem does not specify. 
        # The note says: "Do not include separate flight entries in the JSON."
        # We assume that for a day, we list all cities that are visited on that day.
        # But the example output format is not provided.
        #
        # We will output for each day, the list of cities that the traveler is in on that day.
        # However, the problem says: "a list of day-place mappings". We will output a list of dictionaries for each day?
        # But the problem says: "a list of day-place mappings", meaning a list where each element is a mapping from day to place? 
        # Alternatively, we can output a dictionary: { "itinerary": [ {"day": 1, "place": "Prague"}, ... ] }
        # But for day3, we are in both Prague and London. So we might have two entries for day3? 
        #
        # Let's re-read: "a list of day-place mappings". We interpret as a list of dictionaries, each dict has a day and a place. 
        # And if a day has multiple places, then there are multiple entries for that day.
        #
        # However, the problem says: "When you fly from city A to city B on day X, that day counts for BOTH cities."
        # So we must include both.
        #
        # We'll create a list of dicts: [{"day": 1, "place": "Prague"}, ...]
        result_list = []
        for day in range(1, 27):
            if day in day_place:
                for city in day_place[day]:
                    result_list.append({"day": day, "place": city})
            else:
                # This should not happen, but for safety
                pass
        
        # Also include the fixed cities: but they are already in the itinerary list.
        # Create the final dictionary
        result_dict = {
            "itinerary": result_list
        }
        
        print(json.dumps(result_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()