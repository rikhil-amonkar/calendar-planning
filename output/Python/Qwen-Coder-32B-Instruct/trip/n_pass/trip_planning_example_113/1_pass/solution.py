import json

def calculate_itinerary():
    # Input variables
    total_days = 12
    naples_days = 3
    seville_days = 4
    milan_days = 7
    show_start_day = 9
    show_end_day = 12

    # Initialize itinerary
    itinerary = []

    # Calculate days in each city
    # Start with Naples
    itinerary.append({"day_range": f"Day 1-{naples_days}", "place": "Naples"})
    
    # Move to Milan after Naples
    milan_start_day = naples_days
    milan_end_day = milan_start_day + milan_days - 1
    itinerary.append({"day_range": f"Day {milan_start_day}-{milan_end_day}", "place": "Milan"})
    
    # Move to Seville for the show
    seville_start_day = show_start_day
    seville_end_day = show_end_day
    itinerary.append({"day_range": f"Day {seville_start_day}-{seville_end_day}", "place": "Seville"})

    # Adjust Seville stay if needed
    if seville_start_day > milan_end_day + 1:
        # If there's a gap, fill it with Milan
        extra_milan_days = seville_start_day - milan_end_day - 1
        itinerary.insert(1, {"day_range": f"Day {milan_end_day + 1}-{milan_end_day + extra_milan_days}", "place": "Milan"})
        milan_end_day += extra_milan_days
    
    # Ensure the total days match
    if milan_end_day < show_start_day - 1:
        # Fill any remaining days before the show with Seville
        remaining_days = show_start_day - milan_end_day - 1
        seville_start_day -= remaining_days
        itinerary[-1]["day_range"] = f"Day {seville_start_day}-{seville_end_day}"
    
    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary}, indent=4)

# Run the function and print the result
print(calculate_itinerary())