import json

def plan_trip():
    # Input parameters
    total_days = 11
    days_in_seville = 6
    days_in_paris = 2
    days_in_krakow = 5
    krakow_workshop_range = (1, 5)  # Workshop must be between day 1 and day 5
    
    # Direct flights: Krakow <-> Paris, Paris <-> Seville
    # So the possible transitions are:
    # Krakow -> Paris -> Seville
    # Seville -> Paris -> Krakow
    
    # Since the workshop is in Krakow between day 1-5, Krakow must be visited first or last.
    # But if Krakow is last, we can't have the workshop in day 1-5 because the trip is 11 days.
    # So Krakow must be first.
    
    # Possible itinerary: Krakow -> Paris -> Seville
    
    # Assign days to Krakow first (must include day 1-5)
    # Since Krakow is first, the workshop is satisfied if we stay in Krakow for days 1-5.
    # But we have total 5 days in Krakow, so the remaining days must be in Paris and Seville.
    
    # Days in Krakow: day 1 to day 5 (5 days)
    # Then fly to Paris on day 6 (spend day 6 in Paris and Krakow)
    # Days in Paris: day 6 to day 7 (2 days, including day 6 as transition)
    # Then fly to Seville on day 8 (spend day 8 in Paris and Seville)
    # Days in Seville: day 8 to day 11 (6 days, including day 8 as transition)
    
    # Verify:
    # Krakow: day 1-5 (5 days)
    # Paris: day 6-7 (2 days)
    # Seville: day 8-11 (4 days + day 8 transition = 5 days? Wait, no.
    # Actually, day 8 is spent in Paris and Seville, so it counts for both.
    # So Seville is day 8-11: 4 days (8,9,10,11), but day 8 is also in Paris.
    # So total Seville days: 4 (but we need 6). This doesn't work.
    
    # Alternative: stay longer in Paris or adjust transitions.
    # Maybe fly to Paris earlier.
    
    # Let's try:
    # Krakow: day 1-5 (5 days)
    # Fly to Paris on day 6 (day 6: Krakow and Paris)
    # Paris: day 6-7 (2 days, including day 6)
    # Fly to Seville on day 8 (day 8: Paris and Seville)
    # Seville: day 8-11 (4 days, including day 8)
    # Total Seville days: 4 (need 6). Not enough.
    
    # Another approach: Krakow first, then Seville, then Paris.
    # But no direct flight from Krakow to Seville.
    
    # Only option is Krakow -> Paris -> Seville.
    # To get 6 days in Seville, we need to minimize Paris days.
    # But we need 2 days in Paris.
    # So:
    # Krakow: day 1-5 (5 days)
    # Fly to Paris on day 6 (day 6: Krakow and Paris)
    # Paris: day 6-7 (2 days, including day 6)
    # Fly to Seville on day 8 (day 8: Paris and Seville)
    # Seville: day 8-13 (but total days is 11)
    # Wait, no: day 8-11 is 4 days in Seville (8,9,10,11), but day 8 is also Paris.
    # So total Seville days: 4 (need 6). Impossible.
    
    # The only way to get 6 days in Seville is to have Seville days from day X to day X+5 (6 days).
    # But with the flight constraints, the only way is:
    # Krakow -> Paris -> Seville.
    # Krakow: day 1-5 (5 days)
    # Paris: day 6-7 (2 days)
    # Seville: day 8-11 (4 days)
    # Total Seville days: 4 (need 6). Not possible.
    
    # So the constraints cannot be satisfied exactly. We must prioritize:
    # 1. Workshop in Krakow day 1-5 (must be satisfied)
    # 2. Then try to get as close as possible to the other constraints.
    
    # Best possible itinerary:
    itinerary = [
        {"day_range": "Day 1-5", "place": "Krakow"},
        {"day_range": "Day 6-7", "place": "Paris"},
        {"day_range": "Day 8-11", "place": "Seville"}
    ]
    
    # Calculate actual days spent in each city:
    actual_krakow = 5
    actual_paris = 2
    actual_seville = 4
    
    # Check if constraints are satisfied:
    if (actual_krakow == days_in_krakow and 
        actual_paris == days_in_paris and 
        actual_seville == days_in_seville):
        pass  # all good
    else:
        # Adjust itinerary to prioritize workshop and then closest to constraints
        pass  # in this case, the above is the closest possible
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    trip_plan = plan_trip()
    print(json.dumps(trip_plan))