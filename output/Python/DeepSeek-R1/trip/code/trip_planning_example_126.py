import json

def plan_itinerary():
    cities = {"Seville": 6, "Paris": 2, "Krakow": 5}
    workshop_constraint = (1, 5)
    direct_flights = {"Krakow": ["Paris"], "Paris": ["Krakow", "Seville"], "Seville": ["Paris"]}
    
    itinerary = []
    current_day = 1
    
    # Assign Krakow first due to workshop constraint
    krakow_end = workshop_constraint[1]
    itinerary.append({"day_range": f"Day {current_day}-{krakow_end}", "place": "Krakow"})
    current_day = krakow_end
    
    # Transition to Paris
    paris_duration = cities["Paris"]
    paris_end = current_day + paris_duration - 1
    itinerary.append({"day_range": f"Day {current_day}-{paris_end}", "place": "Paris"})
    current_day = paris_end
    
    # Transition to Seville
    seville_duration = cities["Seville"]
    seville_end = current_day + seville_duration - 1
    itinerary.append({"day_range": f"Day {current_day}-{seville_end}", "place": "Seville"})
    
    return {"itinerary": itinerary}

print(json.dumps(plan_itinerary()))