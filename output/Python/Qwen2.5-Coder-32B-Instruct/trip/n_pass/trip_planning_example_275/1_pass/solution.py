import json

def calculate_itinerary():
    # Define the constraints
    total_days = 14
    split_days = 5
    vilnius_days = 4
    santorini_days = 2
    madrid_days = 6
    conference_days = [13, 14]
    
    # Initialize the itinerary
    itinerary = []
    
    # Start in Vilnius for 4 days (Day 1-4)
    itinerary.append({"day_range": f"Day 1-{vilnius_days}", "place": "Vilnius"})
    
    # Fly from Vilnius to Split on Day 4, spend 1 more day in Split (Day 4-5)
    itinerary.append({"day_range": f"Day {vilnius_days}-{vilnius_days + 1}", "place": "Split"})
    
    # Stay in Split for 4 more days (Day 5-8)
    itinerary.append({"day_range": f"Day {vilnius_days + 1}-{vilnius_days + split_days - 1}", "place": "Split"})
    
    # Fly from Split to Madrid on Day 8, spend 1 more day in Madrid (Day 8-9)
    itinerary.append({"day_range": f"Day {vilnius_days + split_days - 1}-{vilnius_days + split_days}", "place": "Madrid"})
    
    # Stay in Madrid for 5 more days (Day 9-13)
    itinerary.append({"day_range": f"Day {vilnius_days + split_days}-{vilnius_days + split_days + madrid_days - 4}", "place": "Madrid"})
    
    # Fly from Madrid to Santorini on Day 13, attend conference (Day 13-14)
    itinerary.append({"day_range": f"Day {vilnius_days + split_days + madrid_days - 4}-{total_days}", "place": "Santorini"})
    
    return itinerary

# Calculate the itinerary
itinerary = calculate_itinerary()

# Output the result as a JSON-formatted dictionary
output = {"itinerary": itinerary}
print(json.dumps(output))