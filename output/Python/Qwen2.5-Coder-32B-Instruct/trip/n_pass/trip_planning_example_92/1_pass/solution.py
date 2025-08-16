import json

def calculate_itinerary():
    # Input variables
    total_days = 12
    stay_riga = 5
    stay_vilnius = 7
    stay_dublin = 2
    
    # Direct flights: Dublin <-> Riga, Riga -> Vilnius
    
    # Initialize itinerary list
    itinerary = []
    
    # Start in Dublin for 2 days (Day 1-2)
    itinerary.append({"day_range": f"Day 1-{stay_dublin}", "place": "Dublin"})
    
    # Fly from Dublin to Riga on Day 2, stay in Riga for 5 days (Day 2-6)
    itinerary.append({"day_range": f"Day 2-{stay_dublin + stay_riga - 1}", "place": "Riga"})
    
    # Fly from Riga to Vilnius on Day 6, stay in Vilnius for 7 days (Day 6-12)
    itinerary.append({"day_range": f"Day 6-{total_days}", "place": "Vilnius"})
    
    return itinerary

# Calculate and print the itinerary in JSON format
itinerary_result = {"itinerary": calculate_itinerary()}
print(json.dumps(itinerary_result))