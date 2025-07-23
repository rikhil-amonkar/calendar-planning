import json

def plan_trip():
    # Input parameters
    total_days = 10
    london_days = 3
    santorini_days = 6
    istanbul_days = 3
    conference_days = [5, 10]
    
    # Direct flights
    direct_flights = {
        "Istanbul": ["London"],
        "London": ["Istanbul", "Santorini"],
        "Santorini": ["London"]
    }
    
    # Initialize itinerary
    itinerary = []
    
    # Revised plan:
    # 1. Start in Santorini (days 1-5) to cover first conference day
    # 2. Fly to London (day 6)
    # 3. Stay in London (days 6-8)
    # 4. Fly to Istanbul (day 9)
    # 5. Stay in Istanbul (days 9-10)
    # 6. Fly back to Santorini via London (day 10) for second conference day
    
    # Day 1-5: Santorini (covers conference day 5)
    itinerary.extend([{"day": day, "location": "Santorini"} for day in range(1, 6)])
    
    # Day 6: Travel to London
    itinerary.append({"day": 6, "location": "Santorini", "action": "Fly to London"})
    itinerary.append({"day": 6, "location": "London"})
    
    # Day 7-8: London
    itinerary.extend([{"day": day, "location": "London"} for day in range(7, 9)])
    
    # Day 9: Travel to Istanbul
    itinerary.append({"day": 9, "location": "London", "action": "Fly to Istanbul"})
    itinerary.append({"day": 9, "location": "Istanbul"})
    
    # Day 10: Travel back to Santorini via London for conference
    itinerary.append({"day": 10, "location": "Istanbul", "action": "Fly to London then to Santorini"})
    itinerary.append({"day": 10, "location": "Santorini"})
    
    # Verify the counts
    locations = [item["location"] for item in itinerary if "action" not in item]
    london_count = locations.count("London")
    santorini_count = locations.count("Santorini")
    istanbul_count = locations.count("Istanbul")
    
    # Verify conference days
    conf_days_ok = all(any(item["day"] == day and item["location"] == "Santorini" 
                      for item in itinerary) for day in conference_days)
    
    if (london_count == london_days and 
        santorini_count == santorini_days and 
        istanbul_count == istanbul_days and 
        conf_days_ok):
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

result = plan_trip()
print(json.dumps(result, indent=2))