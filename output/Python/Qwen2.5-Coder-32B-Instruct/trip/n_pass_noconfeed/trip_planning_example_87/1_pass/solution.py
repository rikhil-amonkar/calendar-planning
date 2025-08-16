import json

def calculate_itinerary():
    # Input constraints
    total_days = 7
    days_in_riga = 2
    days_in_amsterdam = 2
    days_in_mykonos = 5
    
    # Direct flights available
    flights = {
        ('Riga', 'Amsterdam'): True,
        ('Amsterdam', 'Mykonos'): True
    }
    
    # Initialize itinerary
    itinerary = []
    
    # Start in Riga for 2 days (Day 1-2)
    itinerary.append({"day_range": f"Day 1-{days_in_riga}", "place": "Riga"})
    
    # Move from Riga to Amsterdam (Day 2-3)
    itinerary.append({"day_range": f"Day {days_in_riga}-{days_in_riga + 1}", "place": "Amsterdam"})
    
    # Stay in Amsterdam for 1 more day (Day 3-4)
    itinerary.append({"day_range": f"Day {days_in_riga + 1}-{days_in_riga + days_in_amsterdam}", "place": "Amsterdam"})
    
    # Move from Amsterdam to Mykonos (Day 4-5)
    itinerary.append({"day_range": f"Day {days_in_riga + days_in_amsterdam}-{days_in_riga + days_in_amsterdam + 1}", "place": "Mykonos"})
    
    # Stay in Mykonos for the remaining days (Day 5-7)
    last_day = days_in_riga + days_in_amsterdam + days_in_mykonos
    itinerary.append({"day_range": f"Day {days_in_riga + days_in_amsterdam + 1}-{last_day}", "place": "Mykonos"})
    
    return {"itinerary": itinerary}

# Calculate and print the itinerary in JSON format
print(json.dumps(calculate_itinerary(), indent=4))