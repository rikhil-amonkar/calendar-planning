import json

def plan_trip():
    # Input parameters
    total_days = 15
    stuttgart_days = 6
    seville_days = 7
    manchester_days = 4
    meet_friend_stuttgart_range = (1, 6)
    
    # Direct flights
    direct_flights = {
        'Manchester': ['Seville', 'Stuttgart'],
        'Seville': ['Manchester'],
        'Stuttgart': ['Manchester']
    }
    
    # Calculate the order of visits based on flight connections and constraints
    # We need to start or end in Stuttgart to meet the friend between day 1-6
    # Possible sequences:
    # 1. Stuttgart -> Manchester -> Seville
    # 2. Manchester -> Stuttgart -> Seville (but Seville is not connected to Stuttgart)
    # 3. Seville -> Manchester -> Stuttgart
    # Option 1 is feasible
    
    # Option 1: Stuttgart -> Manchester -> Seville
    # Check if the friend meeting is possible in Stuttgart in the first 6 days
    itinerary = []
    
    # Start in Stuttgart
    stuttgart_start = 1
    stuttgart_end = stuttgart_start + stuttgart_days - 1
    itinerary.append({
        'day_range': f"Day {stuttgart_start}-{stuttgart_end}",
        'place': 'Stuttgart'
    })
    
    # Fly to Manchester on day stuttgart_end
    manchester_start = stuttgart_end
    manchester_end = manchester_start + manchester_days - 1
    itinerary.append({
        'day_range': f"Day {manchester_start}-{manchester_end}",
        'place': 'Manchester'
    })
    
    # Fly to Seville on day manchester_end
    seville_start = manchester_end
    seville_end = seville_start + seville_days - 1
    if seville_end > total_days:
        # This sequence doesn't work, try another
        pass
    else:
        itinerary.append({
            'day_range': f"Day {seville_start}-{seville_end}",
            'place': 'Seville'
        })
        # Verify friend meeting constraint
        if meet_friend_stuttgart_range[0] <= stuttgart_end <= meet_friend_stuttgart_range[1]:
            return {'itinerary': itinerary}
    
    # Option 3: Seville -> Manchester -> Stuttgart
    itinerary = []
    seville_start = 1
    seville_end = seville_start + seville_days - 1
    itinerary.append({
        'day_range': f"Day {seville_start}-{seville_end}",
        'place': 'Seville'
    })
    
    # Fly to Manchester on day seville_end
    manchester_start = seville_end
    manchester_end = manchester_start + manchester_days - 1
    itinerary.append({
        'day_range': f"Day {manchester_start}-{manchester_end}",
        'place': 'Manchester'
    })
    
    # Fly to Stuttgart on day manchester_end
    stuttgart_start = manchester_end
    stuttgart_end = stuttgart_start + stuttgart_days - 1
    if stuttgart_end > total_days:
        # This sequence doesn't work
        pass
    else:
        itinerary.append({
            'day_range': f"Day {stuttgart_start}-{stuttgart_end}",
            'place': 'Stuttgart'
        })
        # Verify friend meeting constraint
        if meet_friend_stuttgart_range[0] <= stuttgart_end <= meet_friend_stuttgart_range[1]:
            return {'itinerary': itinerary}
    
    # If no valid itinerary found (shouldn't happen with given constraints)
    return {'itinerary': []}

result = plan_trip()
print(json.dumps(result))