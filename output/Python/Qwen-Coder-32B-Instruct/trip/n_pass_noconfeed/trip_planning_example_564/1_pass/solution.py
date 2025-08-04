import json

def calculate_itinerary():
    # Define the constraints
    total_days = 16
    stay_istanbul = 2
    istanbul_visit_days = (6, 7)
    stay_rome = 3
    stay_seville = 4
    stay_naples = 7
    stay_santorini = 4
    santorini_wedding_days = (13, 16)
    
    # Define the direct flight connections
    flights = {
        'Rome': ['Santorini', 'Seville', 'Naples', 'Istanbul'],
        'Seville': ['Rome'],
        'Istanbul': ['Naples'],
        'Naples': ['Santorini', 'Rome', 'Istanbul'],
        'Santorini': ['Rome', 'Naples']
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Start in Istanbul for the first 5 days to align with the visit
    itinerary.append({"day_range": f"Day {current_day}-{current_day + 4}", "place": "Istanbul"})
    current_day += 5
    
    # Visit Istanbul for 2 days between day 6 and day 7
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_istanbul - 1}", "place": "Istanbul"})
    current_day += stay_istanbul
    
    # Move to Naples after Istanbul
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_naples - 1}", "place": "Naples"})
    current_day += stay_naples
    
    # Move to Rome after Naples
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_rome - 1}", "place": "Rome"})
    current_day += stay_rome
    
    # Move to Seville after Rome
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_seville - 1}", "place": "Seville"})
    current_day += stay_seville
    
    # Move to Santorini for the wedding and remaining days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_santorini - 1}", "place": "Santorini"})
    current_day += stay_santorini
    
    return itinerary

# Calculate the itinerary
itinerary = calculate_itinerary()

# Output the result as a JSON-formatted dictionary
output = {"itinerary": itinerary}
print(json.dumps(output))