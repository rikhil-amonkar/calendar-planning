import json
from itertools import permutations

def main():
    # Define cities and their required days with constraints
    cities = {
        "Copenhagen": {
            "total_days": 5,
            "constraints": [{"type": "meet", "day_range": (11, 15)}],
            "must_include": True
        },
        "Geneva": {
            "total_days": 3,
            "constraints": [],
            "must_include": False
        },
        "Mykonos": {
            "total_days": 2,
            "constraints": [{"type": "conference", "day_range": (27, 28)}],
            "must_include": True
        },
        "Naples": {
            "total_days": 4,
            "constraints": [{"type": "relatives", "day_range": (5, 8)}],
            "must_include": True
        },
        "Prague": {
            "total_days": 2,
            "constraints": [],
            "must_include": False
        },
        "Dubrovnik": {
            "total_days": 3,
            "constraints": [],
            "must_include": False
        },
        "Athens": {
            "total_days": 4,
            "constraints": [{"type": "workshop", "day_range": (8, 11)}],
            "must_include": True
        },
        "Santorini": {
            "total_days": 5,
            "constraints": [],
            "must_include": False
        },
        "Brussels": {
            "total_days": 4,
            "constraints": [],
            "must_include": False
        },
        "Munich": {
            "total_days": 5,
            "constraints": [],
            "must_include": False
        }
    }

    # Define direct flights as a graph
    direct_flights = {
        "Copenhagen": ["Dubrovnik", "Brussels", "Naples", "Prague", "Athens", "Geneva", "Munich", "Santorini"],
        "Brussels": ["Copenhagen", "Naples", "Prague", "Athens", "Munich", "Geneva"],
        "Prague": ["Geneva", "Athens", "Copenhagen", "Brussels", "Munich"],
        "Geneva": ["Prague", "Athens", "Mykonos", "Naples", "Dubrovnik", "Munich", "Brussels", "Copenhagen", "Santorini"],
        "Athens": ["Geneva", "Dubrovnik", "Mykonos", "Naples", "Prague", "Brussels", "Munich", "Santorini", "Copenhagen"],
        "Naples": ["Dubrovnik", "Mykonos", "Copenhagen", "Athens", "Munich", "Geneva", "Santorini", "Brussels"],
        "Dubrovnik": ["Copenhagen", "Naples", "Athens", "Geneva", "Munich"],
        "Mykonos": ["Geneva", "Naples", "Athens", "Munich"],
        "Santorini": ["Geneva", "Athens", "Naples", "Copenhagen"],
        "Munich": ["Dubrovnik", "Brussels", "Prague", "Athens", "Geneva", "Copenhagen", "Mykonos", "Naples"]
    }

    # Must include cities
    must_include = [city for city in cities if cities[city]["must_include"]]
    
    # Try different orders of must_include cities to find a valid itinerary
    for city_order in permutations(must_include):
        current_day = 1
        itinerary = []
        valid = True
        
        # Add Naples first (must be days 5-8)
        if "Naples" in city_order:
            naples_idx = city_order.index("Naples")
            if naples_idx != 0:
                # Try to place cities before Naples
                for city in city_order[:naples_idx]:
                    city_days = cities[city]["total_days"]
                    if city == "Athens":
                        # Athens must include days 8-11, but we're before Naples (5-8)
                        # This won't work, so skip this permutation
                        valid = False
                        break
                    itinerary.append({
                        "day_range": f"Day {current_day}-{current_day + city_days - 1}",
                        "place": city
                    })
                    current_day += city_days
                if not valid:
                    continue
            
            # Add Naples (must be days 5-8)
            if current_day > 5:
                valid = False
                continue
            # Adjust to make sure Naples starts on day 5
            if current_day < 5:
                # Add filler city (Geneva) for days 1-4
                if "Geneva" not in direct_flights.get("Naples", []):
                    valid = False
                    continue
                itinerary.append({
                    "day_range": "Day 1-4",
                    "place": "Geneva"
                })
                current_day = 5
            
            itinerary.append({
                "day_range": "Day 5-8",
                "place": "Naples"
            })
            current_day = 9
            
            # Add remaining cities
            for city in city_order[naples_idx+1:]:
                city_days = cities[city]["total_days"]
                if city == "Athens":
                    # Athens must include days 8-11
                    if current_day > 8:
                        valid = False
                        break
                    # Adjust to make sure Athens covers 8-11
                    if current_day < 8:
                        # Need to add a city that connects from Naples to Athens
                        if "Athens" not in direct_flights.get("Naples", []):
                            valid = False
                            break
                        # Just proceed with Athens starting on day 8
                        current_day = 8
                    itinerary.append({
                        "day_range": f"Day {current_day}-{current_day + city_days - 1}",
                        "place": city
                    })
                    current_day += city_days
                elif city == "Copenhagen":
                    # Copenhagen must include days 11-15
                    if current_day > 11:
                        valid = False
                        break
                    if current_day < 11:
                        # Need to add cities that connect to Copenhagen
                        prev_city = itinerary[-1]["place"]
                        possible_connectors = [c for c in direct_flights[prev_city] 
                                              if c in direct_flights and "Copenhagen" in direct_flights[c]
                                              and cities[c]["total_days"] <= (11 - current_day)]
                        if not possible_connectors:
                            valid = False
                            break
                        # Add the first possible connector
                        connector = possible_connectors[0]
                        connector_days = cities[connector]["total_days"]
                        itinerary.append({
                            "day_range": f"Day {current_day}-{current_day + connector_days - 1}",
                            "place": connector
                        })
                        current_day += connector_days
                        if current_day > 11:
                            valid = False
                            break
                    itinerary.append({
                        "day_range": f"Day {current_day}-{current_day + city_days - 1}",
                        "place": city
                    })
                    current_day += city_days
                elif city == "Mykonos":
                    # Mykonos must be days 27-28 (last in itinerary)
                    continue
                else:
                    itinerary.append({
                        "day_range": f"Day {current_day}-{current_day + city_days - 1}",
                        "place": city
                    })
                    current_day += city_days
            
            # Add Mykonos at the end (days 27-28)
            if current_day > 27:
                valid = False
                continue
            # Add cities to fill up to day 26
            while current_day < 27:
                prev_city = itinerary[-1]["place"]
                possible_next = [c for c in direct_flights[prev_city] 
                               if c != "Mykonos" and cities[c]["total_days"] <= (27 - current_day)]
                if not possible_next:
                    valid = False
                    break
                # Add the first possible city
                next_city = possible_next[0]
                next_days = cities[next_city]["total_days"]
                itinerary.append({
                    "day_range": f"Day {current_day}-{current_day + next_days - 1}",
                    "place": next_city
                })
                current_day += next_days
            
            if not valid:
                continue
            
            # Add Mykonos
            prev_city = itinerary[-1]["place"]
            if "Mykonos" not in direct_flights.get(prev_city, []):
                valid = False
                continue
            itinerary.append({
                "day_range": "Day 27-28",
                "place": "Mykonos"
            })
            
            # Verify all must_include cities are present
            included_cities = [item["place"] for item in itinerary]
            for city in must_include:
                if city not in included_cities:
                    valid = False
                    break
            
            if valid:
                # Verify flight connections
                for i in range(1, len(itinerary)):
                    current = itinerary[i]["place"]
                    prev = itinerary[i-1]["place"]
                    if current not in direct_flights.get(prev, []):
                        valid = False
                        break
                
                if valid:
                    print(json.dumps({"itinerary": itinerary}, indent=2))
                    return
    
    # If no valid itinerary found
    print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()