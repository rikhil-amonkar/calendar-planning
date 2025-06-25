import json

def compute_itinerary(seville_days, paris_days, krakow_days, workshop_days, direct_flights):
    """
    Compute the itinerary for a trip to Krakow, Paris, and Seville.

    The itinerary must cover exactly 11 days. The trip starts in Krakow, then
    moves to Paris, and finally ends in Seville.

    Parameters:
    seville_days (int): Number of days in Seville.
    paris_days (int): Number of days in Paris.
    krakow_days (int): Number of days in Krakow.
    workshop_days (int): Number of days for the workshop in Krakow.
    direct_flights (dict): Dictionary of direct flights between cities.

    Returns:
    dict: Itinerary for the trip.
    """

    # Calculate the total number of days
    total_days = seville_days + paris_days + krakow_days

    # Check if the total number of days matches the constraint
    if total_days!= 11:
        raise ValueError("The itinerary must cover exactly 11 days.")

    # Calculate the remaining days after the workshop
    remaining_krakow_days = krakow_days - workshop_days

    # Initialize the itinerary
    itinerary = []

    # Add the Krakow segment
    krakow_start = 1
    krakow_end = krakow_start + workshop_days - 1
    itinerary.append({"day_range": f"Day {krakow_start}-{krakow_end}", "place": "Krakow"})

    # Add the remaining Krakow segment
    if remaining_krakow_days > 0:
        krakow_end += 1
        krakow_end += remaining_krakow_days - 1
        itinerary.append({"day_range": f"Day {krakow_end}-{krakow_end + remaining_krakow_days - 1}", "place": "Krakow"})

    # Add the Paris segment
    paris_start = krakow_end + 1
    paris_end = paris_start + paris_days - 1
    itinerary.append({"day_range": f"Day {paris_start}-{paris_end}", "place": "Paris"})

    # Add the Seville segment
    seville_start = paris_end + 1
    seville_end = seville_start + seville_days - 1
    itinerary.append({"day_range": f"Day {seville_start}-{seville_end}", "place": "Seville"})

    return {"itinerary": itinerary}

def main():
    seville_days = 4  # Adjusted to ensure the itinerary covers exactly 11 days
    paris_days = 2
    krakow_days = 5
    workshop_days = 3  # Assuming the workshop lasts 3 days
    direct_flights = {"Krakow": ["Paris", "Seville"], "Paris": ["Krakow", "Seville"], "Seville": ["Krakow", "Paris"]}

    # Ensure the total number of days matches the constraint
    total_days = seville_days + paris_days + krakow_days
    if total_days!= 11:
        raise ValueError("The itinerary must cover exactly 11 days.")

    result = compute_itinerary(seville_days, paris_days, krakow_days, workshop_days, direct_flights)
    print(json.dumps(result, indent=4))

if __name__ == "__main__":
    main()