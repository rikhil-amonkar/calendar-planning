import json
from itertools import permutations

def find_itinerary():
    # Cities and their required stay durations
    cities = {
        'Tallinn': 2,
        'Bucharest': 4,
        'Seville': 5,
        'Stockholm': 5,
        'Munich': 5,  # Note: 'Munich' is spelled as 'Munich' here to match the flight connections
        'Milan': 2
    }
    
    # Flight connections (undirected)
    connections = {
        'Milan': ['Stockholm', 'Munich', 'Seville'],
        'Stockholm': ['Milan', 'Munich', 'Tallinn'],
        'Munich': ['Milan', 'Stockholm', 'Bucharest', 'Seville', 'Tallinn'],
        'Bucharest': ['Munich'],
        'Seville': ['Munich', 'Milan'],
        'Tallinn': ['Stockholm', 'Munich']
    }
    
    # Correcting the flight connections to use consistent city names
    # Note: 'Munich' is the correct spelling, but the connections use 'Munich' and 'Munich' is used in constraints
    # Assuming 'Munich' is the correct spelling throughout
    # The connections are undirected, so we'll make sure both directions are present
    flight_graph = {
        'Milan': ['Stockholm', 'Munich', 'Seville'],
        'Stockholm': ['Milan', 'Munich', 'Tallinn'],
        'Munich': ['Milan', 'Stockholm', 'Bucharest', 'Seville', 'Tallinn'],
        'Bucharest': ['Munich'],
        'Seville': ['Munich', 'Milan'],
        'Tallinn': ['Stockholm', 'Munich']
    }
    
    # Correcting the flight graph to use consistent city names
    flight_graph = {
        'Milan': ['Stockholm', 'Munich', 'Seville'],
        'Stockholm': ['Milan', 'Munich', 'Tallinn'],
        'Munich': ['Milan', 'Stockholm', 'Bucharest', 'Seville', 'Tallinn'],
        'Bucharest': ['Munich'],
        'Seville': ['Munich', 'Milan'],
        'Tallinn': ['Stockholm', 'Munich']
    }
    
    # Constraints
    constraints = [
        ('Bucharest', (1, 4)),  # Bucharest between day 1 and day 4
        ('Munich', (4, 8)),      # Munich between day 4 and day 8
        ('Seville', (8, 12))     # Seville between day 8 and day 12
    ]
    
    # Generate all possible permutations of the cities
    city_list = list(cities.keys())
    for perm in permutations(city_list):
        # Check if the permutation satisfies the flight connections
        valid = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in flight_graph[perm[i]]:
                valid = False
                break
        if not valid:
            continue
        
        # Assign days to each city in the permutation
        itinerary = []
        current_day = 1
        for city in perm:
            duration = cities[city]
            itinerary.append((current_day, current_day + duration - 1, city))
            current_day += duration
        
        # Check if the total days match
        if current_day - 1 != 18:
            continue
        
        # Check constraints
        meets_constraints = True
        for city, (start, end) in constraints:
            found = False
            for s, e, c in itinerary:
                if c == city:
                    # Check if the city's stay overlaps with the constraint range
                    if not (e < start or s > end):
                        found = True
                        break
            if not found:
                meets_constraints = False
                break
        if meets_constraints:
            # Format the itinerary
            formatted_itinerary = []
            for s, e, c in itinerary:
                if s == e:
                    day_range = f"Day {s}"
                else:
                    day_range = f"Day {s}-{e}"
                formatted_itinerary.append({"day_range": day_range, "place": c})
            return {"itinerary": formatted_itinerary}
    
    return {"itinerary": []}

# Run the function and print the result as JSON
result = find_itinerary()
print(json.dumps(result, indent=2))