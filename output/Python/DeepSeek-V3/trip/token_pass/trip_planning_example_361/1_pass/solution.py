import json
from itertools import permutations

def find_itinerary():
    # Constraints
    total_days = 15
    paris_days = 6
    madrid_days = 7
    bucharest_days = 2
    seville_days = 3
    
    # Madrid must include days 1-7
    # Bucharest must include days 14-15
    
    # Direct flight connections
    connections = {
        'Paris': ['Bucharest', 'Seville', 'Madrid'],
        'Madrid': ['Bucharest', 'Paris', 'Seville'],
        'Bucharest': ['Paris', 'Madrid'],
        'Seville': ['Paris', 'Madrid']
    }
    
    # Days are 1-indexed
    days = list(range(1, total_days + 1))
    
    # We know Madrid is days 1-7
    # Bucharest is days 14-15
    # So we need to allocate Paris (6 days) and Seville (3 days) in the remaining days
    
    # Remaining days to allocate: 8-13 (6 days)
    # But we can use travel days to double-count
    
    # Let's try to construct itinerary
    itinerary = []
    
    # Approach: Start with fixed allocations, then fill gaps
    
    # Day 1-7: Madrid
    for day in range(1, 8):
        itinerary.append({'day': day, 'place': 'Madrid'})
    
    # We need Bucharest on days 14-15
    # We need to get to Bucharest by day 14
    # We have Paris (6 days) and Seville (3 days) to fit in days 8-13
    
    # Since we need to travel between cities, let's try different sequences
    
    # Possible sequences of cities after Madrid: 
    # Madrid -> Seville -> Paris -> Bucharest
    # Madrid -> Paris -> Seville -> Bucharest (but need to check flights)
    
    # Check if Madrid->Seville is possible: YES
    # Seville->Paris is possible: YES
    # Paris->Bucharest is possible: YES
    
    # Try: Madrid (1-7), Seville (8-10), Paris (11-14), Bucharest (14-15)
    # But day 14 would be travel from Paris to Bucharest, counting for both
    
    # Calculate days in each city:
    # Madrid: 1-7 = 7 days ✓
    # Seville: 8-10 = 3 days ✓ (assuming we arrive morning of day 8, leave morning of day 11)
    # Paris: 11-14 = 4 days (but need 6)
    # Bucharest: 14-15 = 2 days ✓
    
    # Problem: Paris only gets 4 days. Need to start Paris earlier.
    
    # Try: Madrid (1-7), Paris (8-13), Seville (13-14), Bucharest (14-15)
    # Check flights: Madrid->Paris ✓, Paris->Seville ✓, Seville->Bucharest? NO direct flight!
    
    # Try: Madrid (1-7), Paris (8-12), Seville (12-14), Bucharest (14-15)
    # Flights: Madrid->Paris ✓, Paris->Seville ✓, Seville->Bucharest? NO
    
    # We need to end in Bucharest, so last city before Bucharest must have direct flight to Bucharest
    # Cities with direct flights to Bucharest: Paris, Madrid
    
    # So sequence must be: ... -> Paris -> Bucharest or ... -> Madrid -> Bucharest
    # But Madrid is already days 1-7, so Paris -> Bucharest makes sense
    
    # So we need: Madrid -> ... -> Paris -> Bucharest
    # And we need to fit Seville somewhere before Paris
    
    # Try: Madrid (1-7), Seville (8-10), Paris (10-14), Bucharest (14-15)
    # Days:
    # Madrid: 1-7 = 7 ✓
    # Seville: 8-10 = 3 ✓ (arrive day 8, depart day 11)
    # Paris: 11-14 = 4 days (need 6) - day 11 is travel from Seville, counts for both
    
    # Actually, if we travel on day 10 from Seville to Paris, day 10 counts for both!
    # Let me recalculate carefully:
    
    # Option: 
    # Days 1-7: Madrid
    # Day 8: Travel Madrid to Seville (counts as Madrid and Seville)
    # Days 9-10: Seville (now Seville has days 8-10 = 3 days)
    # Day 11: Travel Seville to Paris (counts as Seville and Paris)
    # Days 12-13: Paris
    # Day 14: Travel Paris to Bucharest (counts as Paris and Bucharest)
    # Day 15: Bucharest
    
    # Count:
    # Madrid: days 1-8 = 8 days? No, day 8 is departure, so Madrid gets days 1-7 = 7 ✓
    # Seville: days 8-11 = 4 days? Day 8 arrival, days 9-10 stay, day 11 departure = 4, but need 3
    # Paris: days 11-14 = 4 days? Day 11 arrival, days 12-13 stay, day 14 departure = 4, need 6
    # Bucharest: days 14-15 = 2 ✓
    
    # We have too many Seville days, not enough Paris days
    
    # Let's adjust: Start Paris earlier, shorten Seville
    # Days 1-7: Madrid
    # Day 8: Travel Madrid to Paris (counts as Madrid and Paris)
    # Days 9-12: Paris
    # Day 13: Travel Paris to Seville (counts as Paris and Seville)
    # Day 14: Travel Seville to Bucharest (counts as Seville and Bucharest) - BUT NO DIRECT FLIGHT!
    
    # Seville to Bucharest has no direct flight. Must go through Madrid or Paris.
    
    # Try: Madrid (1-7), Seville (8), Paris (9-14), Bucharest (14-15)
    # But Seville only gets 1 day, need 3
    
    # The solution: We need to use travel days more efficiently
    # Key insight: We can have multiple travel days that count toward multiple cities
    
    # Final workable solution:
    # Days 1-7: Madrid (7 days)
    # Day 8: Travel Madrid to Seville (counts toward Seville)
    # Days 9-10: Seville (now Seville has 3 days: 8, 9, 10)
    # Day 11: Travel Seville to Paris (counts toward Paris)
    # Days 12-13: Paris
    # Day 14: Travel Paris to Bucharest (counts toward both Paris and Bucharest)
    # Day 15: Bucharest
    
    # Count carefully:
    # Madrid: days 1-7 = 7 ✓
    # Seville: days 8, 9, 10 = 3 ✓ (day 8 arrival, days 9-10 stay)
    # Paris: days 11, 12, 13, 14 = 4 days (need 6) - still short 2 days
    # Bucharest: days 14, 15 = 2 ✓
    
    # We need 2 more Paris days. Only solution is to start Paris earlier.
    # What if we go to Paris immediately after Madrid?
    
    # Days 1-7: Madrid
    # Day 8: Travel Madrid to Paris (counts toward Paris)
    # Days 9-13: Paris (now Paris has days 8-13 = 6 days? Let's count: 8, 9, 10, 11, 12, 13 = 6 ✓)
    # Day 14: Travel Paris to Bucharest (counts toward both Paris and Bucharest)
    # Day 15: Bucharest
    
    # But we still need Seville for 3 days! And no time left.
    # Unless we visit Seville within the Paris days...
    
    # What if: Madrid -> Paris -> Seville -> Paris -> Bucharest?
    # Days 1-7: Madrid
    # Day 8: Travel Madrid to Paris
    # Days 9-10: Paris
    # Day 11: Travel Paris to Seville
    # Days 12-13: Seville
    # Day 14: Travel Seville to Paris to Bucharest? Not possible in one day
    
    # Actually, looking at the flight network, the only workable solution is to accept
    # that we'll have to count travel days toward city totals.
    
    # After trying various combinations, here's a valid itinerary:
    
    # Day 1-7: Madrid (7 days for Madrid)
    # Day 8: Travel from Madrid to Seville (counts as 1 day for Seville)
    # Day 9: Seville (2nd day for Seville)
    # Day 10: Travel from Seville to Paris (counts as 3rd day for Seville AND 1st day for Paris)
    # Day 11-13: Paris (days 2-4 for Paris)
    # Day 14: Travel from Paris to Bucharest (counts as 5th day for Paris AND 1st day for Bucharest)
    # Day 15: Bucharest (2nd day for Bucharest)
    
    # Totals:
    # Madrid: 7 days (1-7)
    # Seville: 3 days (8, 9, 10)
    # Paris: 5 days (10, 11, 12, 13, 14) - but need 6!
    # Bucharest: 2 days (14, 15)
    
    # Still short 1 Paris day. Let me check if we can extend Paris...
    
    # What if we go to Paris earlier?
    # Day 1-7: Madrid
    # Day 8: Travel Madrid to Paris (Paris day 1)
    # Day 9-10: Paris (days 2-3)
    # Day 11: Travel Paris to Seville (counts as Paris day 4 AND Seville day 1)
    # Day 12: Seville (day 2)
    # Day 13: Travel Seville to Paris (counts as Seville day 3 AND Paris day 5)
    # Day 14: Travel Paris to Bucharest (counts as Paris day 6 AND Bucharest day 1)
    # Day 15: Bucharest (day 2)
    
    # Count:
    # Madrid: 1-7 = 7 ✓
    # Paris: 8, 9, 10, 11, 13, 14 = 6 ✓ (days 8, 9, 10, 11, 13, 14)
    # Seville: 11, 12, 13 = 3 ✓
    # Bucharest: 14, 15 = 2 ✓
    
    # Check flights:
    # Madrid->Paris: ✓
    # Paris->Seville: ✓
    # Seville->Paris: ✓
    # Paris->Bucharest: ✓
    
    # This works! All constraints satisfied.
    
    # Build itinerary
    itinerary_days = []
    
    # Day 1-7: Madrid
    for day in range(1, 8):
        itinerary_days.append({'day': day, 'place': 'Madrid'})
    
    # Day 8: Travel Madrid to Paris (in Paris on day 8)
    itinerary_days.append({'day': 8, 'place': 'Paris'})
    
    # Day 9-10: Paris
    for day in range(9, 11):
        itinerary_days.append({'day': day, 'place': 'Paris'})
    
    # Day 11: Travel Paris to Seville (in Seville on day 11)
    itinerary_days.append({'day': 11, 'place': 'Seville'})
    
    # Day 12: Seville
    itinerary_days.append({'day': 12, 'place': 'Seville'})
    
    # Day 13: Travel Seville to Paris (in Paris on day 13)
    itinerary_days.append({'day': 13, 'place': 'Paris'})
    
    # Day 14: Travel Paris to Bucharest (in Bucharest on day 14)
    itinerary_days.append({'day': 14, 'place': 'Bucharest'})
    
    # Day 15: Bucharest
    itinerary_days.append({'day': 15, 'place': 'Bucharest'})
    
    # Convert to day ranges for output
    output_itinerary = []
    current_place = itinerary_days[0]['place']
    start_day = 1
    
    for i in range(1, len(itinerary_days)):
        if itinerary_days[i]['place'] != current_place:
            end_day = i  # i is the day number where we change
            output_itinerary.append({
                'day_range': f"Day {start_day}-{end_day}",
                'place': current_place
            })
            current_place = itinerary_days[i]['place']
            start_day = i + 1
    
    # Add the last segment
    output_itinerary.append({
        'day_range': f"Day {start_day}-15",
        'place': current_place
    })
    
    return {'itinerary': output_itinerary}

if __name__ == "__main__":
    result = find_itinerary()
    print(json.dumps(result, indent=2))