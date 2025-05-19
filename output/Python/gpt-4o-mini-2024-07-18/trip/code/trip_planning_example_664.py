import json

def plan_trip():
    # Define the constraints
    trip_days = 18
    city_durations = {
        "Tallinn": 2,
        "Bucharest": 4,
        "Seville": 5,
        "Stockholm": 5,
        "Munich": 5,
        "Milan": 2,
    }

    visits = [
        {"city": "Tallinn", "days": city_durations["Tallinn"]},
        {"city": "Bucharest", "days": city_durations["Bucharest"], "days_range": (1, 4)},
        {"city": "Seville", "days": city_durations["Seville"], "friends_range": (8, 12)},
        {"city": "Stockholm", "days": city_durations["Stockholm"]},
        {"city": "Munich", "days": city_durations["Munich"], "wedding_range": (4, 8)},
        {"city": "Milan", "days": city_durations["Milan"]},
    ]

    # The full itinerary list
    itinerary = []
    current_day = 1
    
    # Plan the trip based on constraints
    for visit in visits:
        city = visit["city"]
        duration = visit["days"]
        
        # For Bucharest
        if city == "Bucharest":
            itinerary.append({"day_range": f"Day {current_day}-{current_day + duration - 1}", "place": city})
            current_day += duration
        
        # Transition to Munich for the wedding
        elif city == "Munich":
            if current_day <= 4:  # Wedding can be attended
                itinerary.append({"day_range": f"Day {current_day}-{current_day + duration - 1}", "place": city})
                current_day += duration
        
        # For Seville, ensure friends are met
        elif city == "Seville":
            if current_day + duration - 1 <= 12:  # Make sure ends before day 12
                itinerary.append({"day_range": f"Day {current_day}-{current_day + duration - 1}", "place": city})
                current_day += duration
        
        # For Stockholm
        elif city == "Stockholm":
            itinerary.append({"day_range": f"Day {current_day}-{current_day + duration - 1}", "place": city})
            current_day += duration
        
        # For Milan, this should be included last based on flight connection
        elif city == "Milan":
            itinerary.append({"day_range": f"Day {current_day}-{current_day + duration - 1}", "place": city})
            current_day += duration
        
        # For Tallinn, add at the start
        elif city == "Tallinn":
            itinerary.insert(0, {"day_range": f"Day {current_day}-{current_day + duration - 1}", "place": city})
            current_day += duration
    
    # Plan transitions based on direct flights
    transitions = [
        {"flying": f"Day {current_day-2}-{current_day-2}", "from": "Tallinn", "to": "Bucharest"},  # Day 1
        {"flying": f"Day {current_day-1}-{current_day-1}", "from": "Bucharest", "to": "Munich"},  # Day 5
        {"flying": f"Day {current_day-1}-{current_day-1}", "from": "Munich", "to": "Seville"},  # Day 8
        {"flying": f"Day {current_day-1}-{current_day-1}", "from": "Seville", "to": "Stockholm"},  # Day 13
        {"flying": f"Day {current_day-1}-{current_day-1}", "from": "Stockholm", "to": "Milan"},  # Day 18
    ]
    
    # Combine itineraries and transitions
    full_itinerary = []
    
    for part in transitions:
        full_itinerary.append(part)
    for part in itinerary:
        full_itinerary.append(part)

    return json.dumps(full_itinerary, indent=4)

if __name__ == "__main__":
    trip_plan = plan_trip()
    print(trip_plan)