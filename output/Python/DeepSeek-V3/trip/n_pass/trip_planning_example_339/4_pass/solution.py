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
        # Must start with Warsaw due to show on days 1-2
        if order[0] != "Warsaw":
            continue
            
        # Create a temporary copy of city days
        remaining_days = city_days.copy()
        itinerary = []
        day = 1
        
        # Assign Warsaw for days 1-2
        stay_days = min(warsaw_show[1] - day + 1, remaining_days["Warsaw"])
        itinerary.append({
            "day_range": f"Day {day}-{day + stay_days - 1}",
            "place": "Warsaw"
        })
        remaining_days["Warsaw"] -= stay_days
        day += stay_days
        current_city = "Warsaw"
        
        # Try to assign remaining cities with possible splits
        valid = True
        for next_city in order[1:]:
            if (current_city, next_city) not in flight_pairs:
                valid = False
                break
            if remaining_days[next_city] <= 0:
                valid = False
                break
            
            stay_days = remaining_days[next_city]
            
            # If we're going to Riga, make sure we're there during days 11-17
            if next_city == "Riga":
                # Calculate when we would arrive in Riga
                arrival_day = day
                departure_day = arrival_day + stay_days - 1
                
                # Check if this stay covers the wedding period
                if not (arrival_day <= wedding_in_riga[1] and departure_day >= wedding_in_riga[0]):
                    # Try to adjust the stay
                    required_days = wedding_in_riga[1] - max(wedding_in_riga[0], arrival_day) + 1
                    if required_days > stay_days:
                        valid = False
                        break
                    # Adjust stay to cover wedding
                    stay_days = max(stay_days, wedding_in_riga[1] - arrival_day + 1)
                    if stay_days > remaining_days["Riga"]:
                        valid = False
                        break
            
            itinerary.append({
                "day_range": f"Day {day}-{day + stay_days - 1}",
                "place": next_city
            })
            remaining_days[next_city] -= stay_days
            day += stay_days
            current_city = next_city
        
        # Final validation
        if valid and day == total_days + 1 and all(v == 0 for v in remaining_days.values()):
            # Double check Riga wedding constraint
            riga_covered = False
            for item in itinerary:
                if item["place"] == "Riga":
                    start_day = int(item["day_range"].split("-")[0].split(" ")[1])
                    end_day = int(item["day_range"].split("-")[1])
                    if start_day <= wedding_in_riga[1] and end_day >= wedding_in_riga[0]:
                        riga_covered = True
                        break
            if riga_covered:
                valid_itineraries.append(itinerary)
    
    if valid_itineraries:
        return {"itinerary": valid_itineraries[0]}
    else:
        return {"itinerary": []}

result = find_itinerary()
print(json.dumps(result, indent=2))