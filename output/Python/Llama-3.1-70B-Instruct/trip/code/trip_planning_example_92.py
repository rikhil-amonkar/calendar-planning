import json

def calculate_trip_plan(riga_days, vilnius_days, dublin_days):
    total_days = riga_days + vilnius_days + dublin_days

    # Calculate the number of days for each city
    dublin_start_day = 1
    dublin_end_day = dublin_start_day + dublin_days - 1

    # Calculate the day ranges for Riga
    riga_start_day = dublin_end_day + 1
    riga_end_day = riga_start_day + riga_days - 1

    # Calculate the day ranges for Vilnius
    vilnius_start_day = riga_end_day + 1
    vilnius_end_day = vilnius_start_day + vilnius_days - 1

    # Check if the total days add up correctly
    if vilnius_end_day!= total_days:
        raise ValueError("Total days do not add up correctly")

    # Create the trip plan
    trip_plan = [
        {'day_range': f'Day {dublin_start_day}-{dublin_end_day}', 'place': 'Dublin'},
        {'flying': f'Day {dublin_end_day}-{dublin_end_day}', 'from': 'Dublin', 'to': 'Riga'},
        {'day_range': f'Day {riga_start_day}-{riga_end_day}', 'place': 'Riga'},
        {'flying': f'Day {riga_end_day}-{riga_end_day}', 'from': 'Riga', 'to': 'Vilnius'},
        {'day_range': f'Day {vilnius_start_day}-{vilnius_end_day}', 'place': 'Vilnius'}
    ]

    return trip_plan

def main():
    riga_days = 5
    vilnius_days = 7
    dublin_days = 0

    if dublin_days == 0:
        dublin_days = 12 - (riga_days + vilnius_days)

    trip_plan = calculate_trip_plan(riga_days, vilnius_days, dublin_days)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()