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
        
        # We'll handle the cities in order, respecting constraints
        for city in city_order:
            city_info = cities[city]
            days_needed = city_info["total_days"]
            
            # Check constraints for this city
            for constraint in city_info["constraints"]:
                if constraint["type"] == "relatives":  # Naples
                    start_day = constraint["day_range"][0]
                    end_day = constraint["day_range"][1]
                    if current_day > start_day:
                        valid = False
                        break
                    # If we're before the required start day, add filler cities
                    while current_day < start_day:
                        # Find a city that connects from previous to Naples
                        prev_city = itinerary[-1]["place"] if itinerary else None
                        possible_fillers = []
                        if prev_city:
                            possible_fillers = [c for c in direct_flights.get(prev_city, []) 
                                              if c in direct_flights.get("Naples", [])
                                              and not cities[c]["must_include"]
                                              and cities[c]["total_days"] <= (start_day - current_day)]
                        
                        if not possible_fillers:
                            valid = False
                            break
                        
                        # Add the first possible filler city
                        filler = possible_fillers[0]
                        filler_days = cities[filler]["total_days"]
                        itinerary.append({
                            "day_range": f"Day {current_day}-{current_day + filler_days - 1}",
                            "place": filler
                        })
                        current_day += filler_days
                    
                    if not valid:
                        break
                    
                    # Add Naples
                    itinerary.append({
                        "day_range": f"Day {start_day}-{end_day}",
                        "place": city
                    })
                    current_day = end_day + 1
                    
                elif constraint["type"] == "workshop":  # Athens
                    start_day = constraint["day_range"][0]
                    end_day = constraint["day_range"][1]
                    if current_day > start_day:
                        valid = False
                        break
                    # If we're before the required start day, add filler cities
                    while current_day < start_day:
                        # Find a city that connects from previous to Athens
                        prev_city = itinerary[-1]["place"] if itinerary else None
                        possible_fillers = []
                        if prev_city:
                            possible_fillers = [c for c in direct_flights.get(prev_city, []) 
                                              if c in direct_flights.get("Athens", [])
                                              and not cities[c]["must_include"]
                                              and cities[c]["total_days"] <= (start_day - current_day)]
                        
                        if not possible_fillers:
                            valid = False
                            break
                        
                        # Add the first possible filler city
                        filler = possible_fillers[0]
                        filler_days = cities[filler]["total_days"]
                        itinerary.append({
                            "day_range": f"Day {current_day}-{current_day + filler_days - 1}",
                            "place": filler
                        })
                        current_day += filler_days
                    
                    if not valid:
                        break
                    
                    # Add Athens
                    itinerary.append({
                        "day_range": f"Day {start_day}-{end_day}",
                        "place": city
                    })
                    current_day = end_day + 1
                    
                elif constraint["type"] == "meet":  # Copenhagen
                    start_day = constraint["day_range"][0]
                    end_day = constraint["day_range"][1]
                    if current_day > start_day:
                        valid = False
                        break
                    # If we're before the required start day, add filler cities
                    while current_day < start_day:
                        # Find a city that connects from previous to Copenhagen
                        prev_city = itinerary[-1]["place"] if itinerary else None
                        possible_fillers = []
                        if prev_city:
                            possible_fillers = [c for c in direct_flights.get(prev_city, []) 
                                              if c in direct_flights.get("Copenhagen", [])
                                              and not cities[c]["must_include"]
                                              and cities[c]["total_days"] <= (start_day - current_day)]
                        
                        if not possible_fillers:
                            valid = False
                            break
                        
                        # Add the first possible filler city
                        filler = possible_fillers[0]
                        filler_days = cities[filler]["total_days"]
                        itinerary.append({
                            "day_range": f"Day {current_day}-{current_day + filler_days - 1}",
                            "place": filler
                        })
                        current_day += filler_days
                    
                    if not valid:
                        break
                    
                    # Add Copenhagen
                    itinerary.append({
                        "day_range": f"Day {start_day}-{end_day}",
                        "place": city
                    })
                    current_day = end_day + 1
                    
                elif constraint["type"] == "conference":  # Mykonos
                    start_day = constraint["day_range"][0]
                    end_day = constraint["day_range"][1]
                    # Mykonos must be last, we'll handle it separately
                    continue
            
            if not valid:
                break
        
        # Now handle Mykonos (must be days 27-28)
        if valid:
            # Fill days up to 26
            while current_day < 27:
                prev_city = itinerary[-1]["place"] if itinerary else None
                possible_fillers = []
                if prev_city:
                    possible_fillers = [c for c in direct_flights.get(prev_city, []) 
                                      if c in direct_flights.get("Mykonos", [])
                                      and not cities[c]["must_include"]
                                      and cities[c]["total_days"] <= (27 - current_day)]
                
                if not possible_fillers:
                    valid = False
                    break
                
                # Add the first possible filler city
                filler = possible_fillers[0]
                filler_days = cities[filler]["total_days"]
                itinerary.append({
                    "day_range": f"Day {current_day}-{current_day + filler_days - 1}",
                    "place": filler
                })
                current_day += filler_days
            
            if valid:
                # Add Mykonos
                prev_city = itinerary[-1]["place"]
                if "Mykonos" not in direct_flights.get(prev_city, []):
                    valid = False
                else:
                    itinerary.append({
                        "day_range": "Day 27-28",
                        "place": "Mykonos"
                    })
        
        # Verify all must_include cities are present and flight connections are valid
        if valid:
            included_cities = [item["place"] for item in itinerary]
            for city in must_include:
                if city not in included_cities:
                    valid = False
                    break
            
            if valid:
                # Check flight connections
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