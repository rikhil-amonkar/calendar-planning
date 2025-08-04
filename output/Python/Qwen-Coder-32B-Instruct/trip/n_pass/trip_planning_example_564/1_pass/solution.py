import json

def calculate_itinerary():
    # Define the constraints
    total_days = 16
    days_in_istanbul = 2
    istanbul_visit_days = (6, 7)
    days_in_rome = 3
    days_in_seville = 4
    days_in_naples = 7
    days_in_santorini = 4
    santorini_wedding_days = (13, 16)

    # Initialize the itinerary
    itinerary = []

    # Start in Istanbul on day 6 and stay for 2 days
    itinerary.append({"day_range": f"Day {istanbul_visit_days[0]}-{istanbul_visit_days[1]}", "place": "Istanbul"})
    
    # Fly to Naples on day 6 (shared day) and stay until day 12
    itinerary.append({"day_range": f"Day {istanbul_visit_days[1]}-{istanbul_visit_days[1]+days_in_naples-2}", "place": "Naples"})
    
    # Fly to Rome on day 12 (shared day) and stay until day 14
    itinerary.append({"day_range": f"Day {istanbul_visit_days[1]+days_in_naples-2}-{istanbul_visit_days[1]+days_in_naples+days_in_rome-3}", "place": "Rome"})
    
    # Fly to Seville on day 14 (shared day) and stay until day 18 (but we only need 4 days, so we leave on day 18)
    itinerary.append({"day_range": f"Day {istanbul_visit_days[1]+days_in_naples+days_in_rome-3}-{istanbul_visit_days[1]+days_in_naples+days_in_rome-3+days_in_seville}", "place": "Seville"})
    
    # Fly to Naples on day 18 (shared day) and stay until day 24 (but we only need 7 days, so we leave on day 20)
    itinerary.append({"day_range": f"Day {istanbul_visit_days[1]+days_in_naples+days_in_rome-3+days_in_seville}-{istanbul_visit_days[1]+days_in_naples+days_in_rome-3+days_in_seville+days_in_naples}", "place": "Naples"})
    
    # Fly to Santorini on day 20 (shared day) and stay until day 24 (but we only need 4 days, so we leave on day 24)
    itinerary.append({"day_range": f"Day {santorini_wedding_days[0]}-{santorini_wedding_days[1]}", "place": "Santorini"})

    return itinerary

# Calculate the itinerary
itinerary = calculate_itinerary()

# Output the result as a JSON-formatted dictionary
print(json.dumps({"itinerary": itinerary}, indent=4))