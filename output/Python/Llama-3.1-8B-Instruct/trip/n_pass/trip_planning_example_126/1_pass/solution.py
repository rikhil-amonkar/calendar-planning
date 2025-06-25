import json

def compute_itinerary(seville_days, paris_days, krakow_days, workshop_days, direct_flights):
    # Calculate the total number of days
    total_days = seville_days + paris_days + krakow_days

    # Initialize the itinerary
    itinerary = []

    # Add the Krakow segment
    krakow_start = 1
    krakow_end = krakow_start + krakow_days - 1
    if workshop_days == krakow_days:
        krakow_end = krakow_start + workshop_days - 1
    itinerary.append({"day_range": f"Day {krakow_start}-{krakow_end}", "place": "Krakow"})

    # Add the Paris segment
    paris_start = krakow_end + 1
    paris_end = paris_start + paris_days - 1
    if krakow_days - workshop_days > 0:
        paris_start += 1
    itinerary.append({"day_range": f"Day {paris_start}-{paris_end}", "place": "Paris"})

    # Add the Seville segment
    seville_start = paris_end + 1
    seville_end = seville_start + seville_days - 1
    itinerary.append({"day_range": f"Day {seville_start}-{seville_end}", "place": "Seville"})

    return {"itinerary": itinerary}

def main():
    seville_days = 6
    paris_days = 2
    krakow_days = 5
    workshop_days = 3  # Assuming the workshop lasts 3 days
    direct_flights = {"Krakow": ["Paris", "Seville"], "Paris": ["Krakow", "Seville"], "Seville": ["Krakow", "Paris"]}

    result = compute_itinerary(seville_days, paris_days, krakow_days, workshop_days, direct_flights)
    print(json.dumps(result, indent=4))

if __name__ == "__main__":
    main()