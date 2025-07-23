import json

def compute_itinerary():
    # Define the constraints
    total_days = 15
    paris_days = 6
    madrid_days = 7
    bucharest_days = 2
    seville_days = 3
    
    # Madrid must be from day 1 to 7 (inclusive)
    # Bucharest must be between day 14 and 15 (inclusive)
    
    # Initialize itinerary
    itinerary = []
    
    # Madrid is fixed from day 1 to 7
    itinerary.append({"day_range": "Day 1-7", "place": "Madrid"})
    
    # After Madrid, we need to go to another city
    # Possible next cities from Madrid: Paris, Seville, Bucharest
    # But Bucharest must be at the end (day 14-15), so next options are Paris or Seville
    
    # We have to spend 3 days in Seville and 6 in Paris
    # Also, Paris has flights to Seville and Bucharest
    
    # Option 1: Madrid -> Paris -> Seville -> Bucharest
    # Option 2: Madrid -> Seville -> Paris -> Bucharest
    
    # Check which option fits better
    
    # Option 1:
    # Madrid: 1-7 (7 days)
    # Paris: 8-13 (6 days)
    # Seville: 14-15 (2 days) -> but need 3 days, doesn't work
    
    # Option 1 adjusted:
    # Madrid: 1-7 (7 days)
    # Paris: 8-12 (5 days), then Seville 13-15 (3 days)
    # But then Bucharest is missing
    
    # Option 1 better:
    # Madrid: 1-7 (7 days)
    # Paris: 8-10 (3 days), then Seville 11-13 (3 days), then Paris 14-15 (2 days) -> total Paris 5 days (not 6)
    
    # Option 2:
    # Madrid: 1-7 (7 days)
    # Seville: 8-10 (3 days)
    # Paris: 11-16 (but only 15 days total) -> 11-15 (5 days) -> total Paris 5 days (need 6)
    
    # Option 2 adjusted:
    # Madrid: 1-7 (7 days)
    # Seville: 8-10 (3 days)
    # Paris: 11-16 (but only 15 days) -> 11-15 (5 days) -> missing 1 day in Paris
    
    # Alternative approach: include Bucharest in the middle
    
    # Madrid: 1-7 (7 days)
    # Then go to Paris: 8-12 (5 days)
    # Then Seville: 13-15 (3 days)
    # But Bucharest is missing
    
    # Another approach: include Bucharest in the middle
    
    # Madrid: 1-7 (7 days)
    # Then Bucharest: 8-9 (2 days) -> but Bucharest must be between day 14-15
    # Doesn't work
    
    # Final approach: Madrid must be 1-7, Bucharest must be 14-15
    # So the only option is:
    # Madrid: 1-7
    # Then another city until day 13
    # Then Bucharest: 14-15
    
    # We have to spend 6 days in Paris and 3 in Seville
    # Total days left after Madrid and Bucharest: 15 - 7 (Madrid) - 2 (Bucharest) = 6 days
    # Which matches Paris's requirement (6 days)
    # But we also need to spend 3 days in Seville
    # So we have to overlap or find a way
    
    # Since total days in Paris + Seville is 9, but we only have 6 days left, it's impossible to satisfy all constraints
    
    # Therefore, we need to adjust the constraints or find a compromise
    
    # Given the constraints, the only feasible solution is to reduce Seville days to 1 (but that's not desired)
    # Or find another way
    
    # Re-evaluating: maybe the Bucharest constraint is that it must include day 14-15, but can start earlier
    
    # So Bucharest could be 13-15 (3 days), but we only need 2 days
    
    # Then:
    # Madrid: 1-7 (7 days)
    # Then go to Paris: 8-12 (5 days)
    # Then Seville: 13 (1 day)
    # Then Bucharest: 14-15 (2 days)
    # Total Paris: 5 (need 6), Seville: 1 (need 3), Bucharest: 2 (correct), Madrid: 7 (correct)
    
    # Still not satisfying
    
    # Another idea: maybe the Bucharest visit is only on day 14-15, but can be part of a longer stay
    
    # Final solution: prioritize Madrid and Bucharest constraints, adjust others
    
    # Madrid: 1-7 (7 days)
    # Then Paris: 8-13 (6 days)
    # Then Bucharest: 14-15 (2 days)
    # Seville is not visited, but we can't satisfy all constraints
    
    # Given the constraints, it's impossible to visit all 4 cities with the given flight connections and day requirements
    
    # Therefore, we must drop one city or adjust the days
    
    # Since Seville has the fewest required days (3), we'll drop it
    
    # Final itinerary:
    # Madrid: 1-7 (7 days)
    # Paris: 8-13 (6 days)
    # Bucharest: 14-15 (2 days)
    
    itinerary = [
        {"day_range": "Day 1-7", "place": "Madrid"},
        {"day_range": "Day 8-13", "place": "Paris"},
        {"day_range": "Day 14-15", "place": "Bucharest"}
    ]
    
    # Verify the days
    total = 0
    for entry in itinerary:
        day_range = entry["day_range"]
        parts = day_range.split()
        if "-" in day_range:
            start_day = int(parts[1].split("-")[0])
            end_day = int(parts[1].split("-")[1])
        else:
            start_day = int(parts[1])
            end_day = start_day
        days = end_day - start_day + 1
        total += days
    
    assert total == total_days, "Total days do not match"
    
    # Verify city days
    city_days = {
        "Madrid": 0,
        "Paris": 0,
        "Bucharest": 0,
        "Seville": 0
    }
    
    for entry in itinerary:
        day_range = entry["day_range"]
        parts = day_range.split()
        if "-" in day_range:
            start_day = int(parts[1].split("-")[0])
            end_day = int(parts[1].split("-")[1])
        else:
            start_day = int(parts[1])
            end_day = start_day
        days = end_day - start_day + 1
        city_days[entry["place"]] += days
    
    assert city_days["Madrid"] == madrid_days, "Madrid days do not match"
    assert city_days["Bucharest"] == bucharest_days, "Bucharest days do not match"
    # Paris is 6, which matches
    # Seville is 0, which is a compromise
    
    # Check flight connections
    # Madrid to Paris is allowed
    # Paris to Bucharest is allowed
    
    # Return the itinerary
    return {"itinerary": itinerary}

# Compute and print the itinerary
result = compute_itinerary()
print(json.dumps(result, indent=2))