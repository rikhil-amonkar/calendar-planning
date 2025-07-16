import json
from itertools import permutations

def find_itinerary():
    total_days = 17
    city_days = {
        "Riga": 7,
        "Budapest": 7,
        "Paris": 4,
        "Warsaw": 2
    }
    direct_flights = {
        "Warsaw_Budapest": ("Warsaw", "Budapest"),
        "Warsaw_Riga": ("Warsaw", "Riga"),
        "Budapest_Paris": ("Budapest", "Paris"),
        "Warsaw_Paris": ("Warsaw", "Paris"),
        "Paris_Riga": ("Paris", "Riga")
    }
    flight_pairs = [(a, b) for a, b in direct_flights.values()] + [(b, a) for a, b in direct_flights.values()]
    
    # Constraints
    wedding_in_riga = (11, 17)  # Must be in Riga between day 11 and 17
    warsaw_show = (1, 2)  # Must be in Warsaw from day 1 to 2
    
    # Generate all possible city orders (permutations)
    cities = list(city_days.keys())
    possible_orders = permutations(cities)
    
    valid_itineraries = []
    
    for order in possible_orders:
        itinerary = []
        current_city = None
        remaining_days = city_days.copy()
        day = 1
        
        # Check if Warsaw is first (due to show on days 1-2)
        if order[0] != "Warsaw":
            continue
        
        # Assign Warsaw for days 1-2
        if day <= warsaw_show[1]:
            stay_days = min(warsaw_show[1] - day + 1, remaining_days["Warsaw"])
            itinerary.append({
                "day_range": f"Day {day}-{day + stay_days - 1}",
                "place": "Warsaw"
            })
            remaining_days["Warsaw"] -= stay_days
            day += stay_days
            current_city = "Warsaw"
        
        # Try to assign remaining cities
        valid = True
        for next_city in order[1:]:
            if (current_city, next_city) not in flight_pairs:
                valid = False
                break
            if remaining_days[next_city] <= 0:
                valid = False
                break
            
            # Check if next city is Riga and wedding constraints
            if next_city == "Riga":
                if day > wedding_in_riga[1]:
                    valid = False
                    break
                stay_days = min(wedding_in_riga[1] - day + 1, remaining_days["Riga"])
                if day + stay_days - 1 < wedding_in_riga[0]:
                    valid = False
                    break
            else:
                stay_days = remaining_days[next_city]
            
            itinerary.append({
                "day_range": f"Day {day}-{day + stay_days - 1}",
                "place": next_city
            })
            remaining_days[next_city] -= stay_days
            day += stay_days
            current_city = next_city
        
        # Check if all days are assigned and constraints met
        if valid and day == total_days + 1 and all(v == 0 for v in remaining_days.values()):
            # Check Riga wedding constraint
            riga_days = [item for item in itinerary if item["place"] == "Riga"]
            if not riga_days:
                continue
            riga_range = riga_days[0]["day_range"]
            start_day = int(riga_range.split("-")[0].split(" ")[1])
            end_day = int(riga_range.split("-")[1])
            if not (wedding_in_riga[0] <= end_day <= wedding_in_riga[1]):
                continue
            
            valid_itineraries.append(itinerary)
    
    if valid_itineraries:
        return {"itinerary": valid_itineraries[0]}
    else:
        return {"itinerary": []}

result = find_itinerary()
print(json.dumps(result))