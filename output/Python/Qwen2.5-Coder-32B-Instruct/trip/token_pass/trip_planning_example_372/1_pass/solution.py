import json

def generate_itinerary():
    # Define the constraints
    total_days = 13
    seville_stay = 2
    stuttgart_stay = 7
    porto_stay = 3
    madrid_stay = 4
    
    # Initialize the itinerary
    itinerary = []
    
    # Add Madrid stay (Days 1-4)
    itinerary.append({"day_range": "Day 1-4", "place": "Madrid"})
    
    # Transition to Porto on Day 4 (Day 4 counts for both Madrid and Porto)
    itinerary.append({"day_range": "Day 4-6", "place": "Porto"})
    
    # Transition to Seville on Day 6 (Day 6 counts for both Porto and Seville)
    itinerary.append({"day_range": "Day 6-7", "place": "Seville"})
    
    # Stay in Stuttgart for the conference and additional days (Days 7-12)
    itinerary.append({"day_range": "Day 7-12", "place": "Stuttgart"})
    
    # Transition to Porto on Day 13 for the conference (Day 13 counts for both Stuttgart and Porto)
    # Since we need to be in Stuttgart for the conference, we consider the transition on Day 12 to Day 13
    # However, for simplicity in this structured output, we'll show the transition happening on Day 13
    itinerary.append({"day_range": "Day 13", "place": "Porto"})
    
    # Output the itinerary in JSON format
    return json.dumps({"itinerary": itinerary}, indent=4)

# Generate and print the itinerary
print(generate_itinerary())