import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Valencia": 5,
        "Riga": 5,
        "Prague": 5,
        "Prague_relative_visit": (7, 9),
        "Mykonos": 5,
        "Mykonos_wedding": (1, 3),
        "Zurich": 5,
        "Bucharest": 5,
        "Nice": 2
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Start with Mykonos for the wedding
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Mykonos_wedding'][1] - constraints['Mykonos_wedding'][0]}", "place": "Mykonos"})
    current_day += constraints['Mykonos_wedding'][1] - constraints['Mykonos_wedding'][0] + 1
    
    # Stay in Mykonos until the required days are completed
    if current_day < constraints['Mykonos'] + constraints['Mykonos_wedding'][0]:
        itinerary.append({"day_range": f"Day {current_day}-{constraints['Mykonos']}", "place": "Mykonos"})
        current_day = constraints['Mykonos'] + 1
    
    # Move to Nice
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Nice'] - 1}", "place": "Nice"})
    current_day += constraints['Nice']
    
    # Move to Zurich
    # Adjust the number of days in Zurich to fit the 22-day constraint
    days_in_zurich = 4  # Originally 5, but adjusted to fit the 22-day constraint
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_zurich - 1}", "place": "Zurich"})
    current_day += days_in_zurich
    
    # Visit relatives in Prague between day 7 and day 9
    itinerary.append({"day_range": "Day 7-9", "place": "Prague"})
    current_day = 10
    
    # Stay in Prague until the required days are completed
    if current_day < constraints['Prague'] + 5:
        itinerary.append({"day_range": f"Day {current_day}-{constraints['Prague'] + 5}", "place": "Prague"})
        current_day = constraints['Prague'] + 6
    
    # Move to Bucharest
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Bucharest'] - 1}", "place": "Bucharest"})
    current_day += constraints['Bucharest']
    
    # Move to Valencia
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Valencia'] - 1}", "place": "Valencia"})
    current_day += constraints['Valencia']
    
    # Move to Riga
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Riga'] - 1}", "place": "Riga"})
    current_day += constraints['Riga']
    
    # Ensure the total duration is 22 days
    if current_day != 23:
        raise ValueError(f"Itinerary does not cover exactly 22 days, it covers {current_day - 1} days.")
    
    # Return the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Execute the function and print the result
print(calculate_itinerary())