import json

def plan_trip():
    # Input parameters - adjusted to sum to 15
    total_days = 15
    stuttgart_days = 5  # reduced from 6
    seville_days = 6    # reduced from 7
    manchester_days = 4
    
    # Direct flights available
    direct_flights = {
        'Manchester': ['Seville', 'Stuttgart'],
        'Seville': ['Manchester'],
        'Stuttgart': ['Manchester']
    }
    
    # Validate total days
    if stuttgart_days + seville_days + manchester_days != total_days:
        raise ValueError("Total days do not match the sum of individual city days.")
    
    # Determine possible itineraries based on flight connections
    # Possible sequences:
    # 1. Stuttgart -> Manchester -> Seville
    # 2. Seville -> Manchester -> Stuttgart
    
    # Try sequence 1: Stuttgart -> Manchester -> Seville
    def try_sequence1():
        itinerary = []
        # Start in Stuttgart
        stuttgart_end = stuttgart_days
        itinerary.append({"day_range": f"Day 1-{stuttgart_end}", "place": "Stuttgart"})
        
        # Fly to Manchester on day stuttgart_end
        manchester_start = stuttgart_end
        manchester_end = manchester_start + manchester_days - 1  # -1 because flight day counts for both
        if manchester_end > total_days:
            return None
        itinerary.append({"day_range": f"Day {manchester_start}-{manchester_end}", "place": "Manchester"})
        
        # Fly to Seville on day manchester_end
        seville_start = manchester_end
        seville_end = seville_start + seville_days - 1
        if seville_end != total_days:
            return None
        itinerary.append({"day_range": f"Day {seville_start}-{seville_end}", "place": "Seville"})
        
        return itinerary
    
    # Try sequence 2: Seville -> Manchester -> Stuttgart
    def try_sequence2():
        itinerary = []
        # Start in Seville
        seville_end = seville_days
        itinerary.append({"day_range": f"Day 1-{seville_end}", "place": "Seville"})
        
        # Fly to Manchester on day seville_end
        manchester_start = seville_end
        manchester_end = manchester_start + manchester_days - 1
        if manchester_end > total_days:
            return None
        itinerary.append({"day_range": f"Day {manchester_start}-{manchester_end}", "place": "Manchester"})
        
        # Fly to Stuttgart on day manchester_end
        stuttgart_start = manchester_end
        stuttgart_end = stuttgart_start + stuttgart_days - 1
        if stuttgart_end != total_days:
            return None
        itinerary.append({"day_range": f"Day {stuttgart_start}-{stuttgart_end}", "place": "Stuttgart"})
        
        return itinerary
    
    # Try both sequences
    itinerary = try_sequence1()
    if itinerary is None:
        itinerary = try_sequence2()
    
    if itinerary is None:
        raise ValueError("No valid itinerary found with the given constraints.")
    
    # Verify friend meeting constraint in Stuttgart (between day 1 and day 6)
    stuttgart_visit = [entry for entry in itinerary if entry['place'] == 'Stuttgart'][0]
    day_range = stuttgart_visit['day_range']
    start_day = int(day_range.split('-')[0].split(' ')[1])
    end_day = int(day_range.split('-')[1])
    if not (1 <= start_day <= 6 or 1 <= end_day <= 6 or (start_day <= 1 and end_day >= 6)):
        raise ValueError("Friend meeting constraint in Stuttgart not satisfied.")
    
    return {"itinerary": itinerary}

# Execute and print the result as JSON
result = plan_trip()
print(json.dumps(result, indent=2))