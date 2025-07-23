import json
from itertools import permutations

def main():
    # Define the cities and their required days
    cities = {
        "Salzburg": 2,
        "Venice": 5,
        "Bucharest": 4,
        "Brussels": 2,
        "Hamburg": 4,
        "Copenhagen": 4,
        "Nice": 3,
        "Zurich": 5,
        "Naples": 4
    }
    
    # Define the direct flights as a graph
    flight_graph = {
        "Zurich": ["Brussels", "Nice", "Naples", "Copenhagen", "Venice", "Bucharest", "Hamburg"],
        "Brussels": ["Zurich", "Venice", "Bucharest", "Hamburg", "Nice", "Copenhagen", "Naples"],
        "Bucharest": ["Copenhagen", "Hamburg", "Brussels", "Naples", "Zurich"],
        "Venice": ["Brussels", "Naples", "Copenhagen", "Zurich", "Nice", "Hamburg"],
        "Nice": ["Zurich", "Hamburg", "Venice", "Brussels", "Naples", "Copenhagen"],
        "Hamburg": ["Nice", "Bucharest", "Brussels", "Zurich", "Copenhagen", "Venice", "Salzburg"],
        "Copenhagen": ["Bucharest", "Venice", "Zurich", "Hamburg", "Brussels", "Naples", "Nice"],
        "Naples": ["Zurich", "Venice", "Bucharest", "Brussels", "Copenhagen", "Nice"],
        "Salzburg": ["Hamburg"]
    }
    
    # Define the constraints
    constraints = [
        ("Brussels", 21, 22),
        ("Copenhagen", 18, 21),
        ("Nice", 9, 11),
        ("Naples", 22, 25)
    ]
    
    # We'll try to find a valid itinerary by brute-forcing permutations
    # Since 9! is large, we'll limit the permutations to a reasonable number
    city_list = list(cities.keys())
    
    # We'll try to find a valid itinerary by checking permutations
    for perm in permutations(city_list):
        itinerary = []
        current_day = 1
        valid = True
        
        # Check if the permutation satisfies the constraints
        for city in perm:
            days_needed = cities[city]
            
            # Check if the city has constraints
            for const_city, start, end in constraints:
                if city == const_city:
                    if not (current_day <= start and current_day + days_needed - 1 >= end):
                        valid = False
                        break
            
            if not valid:
                break
            
            # Add to itinerary
            itinerary.append({
                "day_range": f"Day {current_day}-{current_day + days_needed - 1}",
                "place": city
            })
            
            current_day += days_needed
        
        if valid and current_day - 1 == 25:
            # Check flight connections
            flight_valid = True
            for i in range(len(perm) - 1):
                from_city = perm[i]
                to_city = perm[i+1]
                if to_city not in flight_graph.get(from_city, []):
                    flight_valid = False
                    break
            
            if flight_valid:
                print(json.dumps({"itinerary": itinerary}))
                return
    
    # If no valid itinerary found (shouldn't happen with given constraints)
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()