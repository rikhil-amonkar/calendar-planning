import json

def plan_trip():
    # Input parameters
    total_days = 12
    brussels_days = 2
    split_days = 5
    barcelona_days = 7
    
    # Direct flight connections
    connections = {
        'Brussels': ['Barcelona'],
        'Barcelona': ['Brussels', 'Split'],
        'Split': ['Barcelona']
    }
    
    # Since Brussels and Split are not directly connected, must go through Barcelona
    # Constraints:
    # 1. Must start in Brussels (conference on day 1-2)
    # 2. Must spend 5 days in Split and 7 in Barcelona
    
    # Possible itineraries:
    # Option 1: Brussels -> Barcelona -> Split -> Barcelona
    # Option 2: Brussels -> Barcelona -> Split (but this doesn't allow 7 days in Barcelona)
    # Option 3: Brussels -> Barcelona -> Split -> Barcelona -> Brussels (but this exceeds total days)
    
    # Only Option 1 fits all constraints
    
    # Calculate day ranges
    # Brussels: Day 1-2 (must be first)
    # Then fly to Barcelona on Day 3 (spend Day 3 in both Brussels and Barcelona)
    # But since Brussels days are fixed at 2, we must leave Brussels on Day 3
    # So Brussels: Day 1-2 (2 days)
    # Barcelona: Day 3 - (3 + x - 1)
    # Then fly to Split on Day 3 + x
    # Split: Day 3 + x - (3 + x + 4) (5 days)
    # Then fly back to Barcelona on Day 3 + x + 5
    # Barcelona: remaining days
    
    # Total days:
    # Brussels: 2 (Day 1-2)
    # Barcelona: x (Day 3 - (2 + x)) + y (after Split)
    # Split: 5 (Day (3 + x) - (3 + x + 4))
    # Total: 2 + x + 5 + y = 12
    # And x + y = 7 (Barcelona total)
    
    # Since flying to Split on Day 3 + x and back on Day 3 + x + 5,
    # the Barcelona days before Split is x, after is y = 7 - x
    # The day flying to Split is counted in Barcelona (x includes it)
    # The day flying back is counted in Split and Barcelona
    
    # Find x such that all constraints are satisfied
    # Minimum x is 1 (must spend at least 1 day in Barcelona before Split)
    # Then y = 7 - x
    
    x = 2  # Chose x=2 to have reasonable stays before and after Split
    y = 7 - x
    
    # Check total days: 2 (Brussels) + x + 5 (Split) + y - 1 (overlap day flying back)
    # Wait, no: the day flying back is counted in both Split and Barcelona, but total days is sum
    # Actually, the total is:
    # Brussels: 2
    # Barcelona before Split: x (includes day flying to Split)
    # Split: 5 (includes day flying back)
    # Barcelona after Split: y - 1 (since day flying back is already counted in Split and Barcelona)
    # So total: 2 + x + 5 + (y - 1) = 2 + x + 5 + (7 - x - 1) = 2 + x + 5 + 6 - x = 13 (too much)
    # So need to adjust
    
    # Alternative approach:
    # Brussels: Day 1-2 (2 days)
    # Fly to Barcelona on Day 3
    # Barcelona: Day 3 - (3 + a - 1)
    # Fly to Split on Day 3 + a
    # Split: Day 3 + a - (3 + a + 4) (5 days)
    # Fly back to Barcelona on Day 3 + a + 5
    # Barcelona: Day 3 + a + 5 - 12
    # Total Barcelona: a + (12 - (3 + a + 5)) = a + (4 - a) = 4 (but need 7)
    # Doesn't work
    
    # Correct calculation:
    # Brussels: Day 1-2 (2 days)
    # Fly to Barcelona on Day 3
    # Barcelona: Day 3 - (3 + a - 1) = a days
    # Fly to Split on Day 3 + a
    # Split: Day 3 + a - (3 + a + 4) = 5 days
    # Fly back to Barcelona on Day 3 + a + 5
    # Barcelona: Day 3 + a + 5 - 12 = 7 - a days
    # Total Barcelona: a + (7 - a) = 7
    # Total days: 2 (Brussels) + a (Barcelona) + 5 (Split) + (7 - a) (Barcelona) = 14
    # But we have 12 days, so overlap is 2 days (the flight days)
    # So the correct way is to count flight days as overlapping
    
    # Final itinerary:
    # Brussels: Day 1-2 (2 days)
    # Day 3: Fly to Barcelona (counts as Barcelona day 1)
    # Barcelona: Day 3 - (3 + a - 1) = a days
    # Day 3 + a: Fly to Split (counts as Barcelona day a and Split day 1)
    # Split: Day 3 + a - (3 + a + 4) = 5 days
    # Day 3 + a + 5: Fly back to Barcelona (counts as Split day 5 and Barcelona day a + 1)
    # Barcelona: Day 3 + a + 5 - 12 = remaining days
    
    # Total:
    # Brussels: 2
    # Barcelona: a (before Split) + (12 - (3 + a + 5) + 1) = a + (5 - a) = 5 (but need 7)
    # Doesn't add up
    
    # Alternative approach: fix the Barcelona days first
    # Total days: 12
    # Brussels: 2 (must be consecutive and start on Day 1)
    # Split: 5
    # Barcelona: 7
    # Since flights are only between Brussels-Barcelona and Barcelona-Split, the sequence must be:
    # Brussels -> Barcelona -> Split -> Barcelona
    
    # Assign:
    # Brussels: Day 1-2
    # Fly to Barcelona on Day 3 (counts as Barcelona day 1)
    # Barcelona: Day 3 - (3 + x - 1) = x days
    # Fly to Split on Day 3 + x (counts as Barcelona day x and Split day 1)
    # Split: Day 3 + x - (3 + x + 4) = 5 days
    # Fly back to Barcelona on Day 3 + x + 5 (counts as Split day 5 and Barcelona day x + 1)
    # Barcelona: Day 3 + x + 5 - 12 = remaining days
    
    # Total Barcelona days: x + (12 - (3 + x + 5) + 1) = x + (5 - x) = 5 (but need 7)
    # So this doesn't work
    
    # Recalculate with overlapping days properly accounted:
    # The correct way is to realize that flight days are counted in both cities
    # So the total "city days" is sum of days in each city minus overlapping days
    # Total city days: 2 (Brussels) + 7 (Barcelona) + 5 (Split) = 14
    # But total trip days is 12, so overlap is 2 days (the two flight days)
    
    # Itinerary:
    # Day 1-2: Brussels (2 days)
    # Day 3: Brussels -> Barcelona (counts as Brussels and Barcelona)
    # Day 4-5: Barcelona (2 days) [total Barcelona so far: 3]
    # Day 6: Barcelona -> Split (counts as Barcelona and Split)
    # Day 7-10: Split (4 days) [total Split so far: 5]
    # Day 11: Split -> Barcelona (counts as Split and Barcelona)
    # Day 12: Barcelona (1 day) [total Barcelona: 5]
    # But this only gives 5 Barcelona days (need 7)
    
    # Alternative itinerary:
    # Day 1-2: Brussels (2)
    # Day 3: Brussels -> Barcelona (Brussels done, Barcelona 1)
    # Day 4-8: Barcelona (5 more, total 6)
    # Day 9: Barcelona -> Split (Barcelona 7, Split 1)
    # Day 10-12: Split (3 more, total 4) → but need 5 Split days
    
    # Another try:
    # Day 1-2: Brussels (2)
    # Day 3: Brussels -> Barcelona (Barcelona 1)
    # Day 4-6: Barcelona (3 more, total 4)
    # Day 7: Barcelona -> Split (Barcelona 5, Split 1)
    # Day 8-11: Split (4 more, total 5)
    # Day 12: Split -> Barcelona (Barcelona 6, Split done)
    # Barcelona total: 6 (need 7)
    
    # Final working itinerary:
    # Day 1-2: Brussels (2)
    # Day 3: Brussels -> Barcelona (Barcelona 1)
    # Day 4-7: Barcelona (4 more, total 5)
    # Day 8: Barcelona -> Split (Barcelona 6, Split 1)
    # Day 9-12: Split (4 more, total 5)
    # Barcelona total: 6 (still need 7)
    
    # It seems impossible to satisfy all constraints with 12 days
    # But let's try one more time:
    # Day 1-2: Brussels (2)
    # Day 3: Brussels -> Barcelona (Barcelona 1)
    # Day 4-8: Barcelona (5 more, total 6)
    # Day 9: Barcelona -> Split (Barcelona 7, Split 1)
    # Day 10-12: Split (3 more, total 4) → Split needs 5
    
    # Conclusion: It's impossible to satisfy all constraints with 12 days
    # The minimal days required is 14 (sum of all city days) - 2 (overlap days) = 12
    # But the overlapping causes the Barcelona days to be short
    
    # Therefore, we need to adjust the constraints or accept that Barcelona days will be less
    
    # For the sake of the exercise, we'll output the closest possible itinerary
    
    itinerary = [
        {"day_range": "Day 1-2", "place": "Brussels"},
        {"day_range": "Day 3", "place": "Brussels -> Barcelona"},
        {"day_range": "Day 4-8", "place": "Barcelona"},
        {"day_range": "Day 9", "place": "Barcelona -> Split"},
        {"day_range": "Day 10-12", "place": "Split"}
    ]
    
    # However, this doesn't meet the Barcelona days requirement
    # So we'll choose the itinerary that meets Brussels and Split exactly, and maximizes Barcelona
    
    optimal_itinerary = [
        {"day_range": "Day 1-2", "place": "Brussels"},
        {"day_range": "Day 3", "place": "Brussels -> Barcelona"},
        {"day_range": "Day 4-7", "place": "Barcelona"},
        {"day_range": "Day 8", "place": "Barcelona -> Split"},
        {"day_range": "Day 9-12", "place": "Split"}
    ]
    
    # Barcelona days: Day 3,4-7,8 → 5 days (Day 8 is also Split)
    # Split days: Day 8-12 → 5 days (Day 8 is also Barcelona)
    # Brussels days: Day 1-3 → 3 days (but constraint is 2)
    
    # This is the closest possible
    
    # Final answer:
    result = {
        "itinerary": [
            {"day_range": "Day 1-2", "place": "Brussels"},
            {"day_range": "Day 3-7", "place": "Barcelona"},
            {"day_range": "Day 8-12", "place": "Split"}
        ]
    }
    
    # This gives:
    # Brussels: 2 days (Day 1-2)
    # Barcelona: 5 days (Day 3-7)
    # Split: 5 days (Day 8-12)
    # Total: 12 days
    # But Barcelona is 5 instead of 7
    
    # Given the constraints, it's impossible to have 2 Brussels, 5 Split, and 7 Barcelona in 12 days
    # So we'll output this as the closest possible
    
    return result

if __name__ == "__main__":
    trip_plan = plan_trip()
    print(json.dumps(trip_plan))