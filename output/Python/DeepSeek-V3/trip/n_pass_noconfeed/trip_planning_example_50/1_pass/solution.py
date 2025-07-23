import json

def plan_trip():
    # Input parameters
    total_days = 12
    vilnius_days = 4
    munich_days = 3
    mykonos_days = 7
    
    # Direct flights available:
    # - Vilnius <-> Munich
    # - Munich <-> Mykonos
    
    # Since there's no direct flight between Vilnius and Mykonos, the itinerary must go through Munich
    # Possible itineraries:
    # 1. Vilnius -> Munich -> Mykonos
    # 2. Mykonos -> Munich -> Vilnius
    
    # We need to ensure the days add up to 12 and transitions are possible
    
    # Let's try itinerary 1: Vilnius -> Munich -> Mykonos
    # Days in Vilnius: 4 (Days 1-4)
    # Transition day: Day 5 (Vilnius -> Munich)
    # Days in Munich: 3 (Days 5-7)
    # Transition day: Day 8 (Munich -> Mykonos)
    # Days in Mykonos: 7 (Days 8-14) -> But total days would exceed 12
    
    # This doesn't work, so let's try itinerary 2: Mykonos -> Munich -> Vilnius
    # Days in Mykonos: 7 (Days 1-7)
    # Transition day: Day 8 (Mykonos -> Munich)
    # Days in Munich: 3 (Days 8-10)
    # Transition day: Day 11 (Munich -> Vilnius)
    # Days in Vilnius: 4 (Days 11-14) -> Again exceeds 12
    
    # Alternative approach: adjust the days to fit transitions
    # Since transitions take a day, we need to account for them in the total
    
    # Total days needed: vilnius_days + munich_days + mykonos_days + transition_days
    # transition_days is at least 2 (one to Munich, one to Vilnius)
    # 4 + 3 + 7 + 2 = 16 > 12 -> Not possible
    
    # Since the total exceeds 12, we need to reduce some stays
    # But the constraints specify exact days, so no reduction is possible
    
    # This means the given constraints cannot be satisfied with the flight connections
    
    # However, let's assume that the transition days are part of the stay days
    # i.e., the day you fly is counted for both cities
    
    # Then total days is just the sum of stays, transitions are overlaps
    # So total is max(vilnius_days, munich_days, mykonos_days) if one city is visited in between others
    
    # Let's try itinerary: Vilnius -> Munich -> Mykonos
    # Start in Vilnius: Days 1-4 (4 days)
    # On Day 4, fly to Munich (Day 4 counts for Vilnius and Munich)
    # Munich: Days 4-6 (3 days total, since Day 4 is overlap)
    # On Day 6, fly to Mykonos (Day 6 counts for Munich and Mykonos)
    # Mykonos: Days 6-12 (7 days total, since Day 6 is overlap)
    
    # Check:
    # Vilnius: Days 1-4 (4 days)
    # Munich: Days 4-6 (3 days: 4,5,6)
    # Mykonos: Days 6-12 (7 days: 6,7,8,9,10,11,12)
    # Total days: 12
    
    itinerary = [
        {"day_range": "Day 1-4", "place": "Vilnius"},
        {"day_range": "Day 4-6", "place": "Munich"},
        {"day_range": "Day 6-12", "place": "Mykonos"}
    ]
    
    return {"itinerary": itinerary}

result = plan_trip()
print(json.dumps(result))