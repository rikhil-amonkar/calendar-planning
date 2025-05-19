import json

def calculate_trip_plan(krakow_days, dubrovnik_days, frankfurt_days, wedding_window):
    total_days = krakow_days + dubrovnik_days + frankfurt_days

    # Calculate the number of days for each city, considering the wedding window in Krakow
    krakow_start_day = 8
    krakow_end_day = krakow_start_day + krakow_days - 1
    wedding_day = (wedding_window[0] + wedding_window[1]) // 2

    # Ensure Krakow is visited last to attend the wedding
    if wedding_day < krakow_start_day or wedding_day > krakow_end_day:
        raise ValueError("Wedding day does not fall within the Krakow visit window")

    # Calculate the day ranges for Frankfurt
    frankfurt_start_day = 1
    frankfurt_end_day = frankfurt_start_day + frankfurt_days - 1

    # Calculate the day ranges for Dubrovnik
    dubrovnik_start_day = frankfurt_end_day + 1
    dubrovnik_end_day = dubrovnik_start_day + dubrovnik_days - 1

    # Check if the total days add up correctly
    if krakow_start_day!= dubrovnik_end_day + 1:
        raise ValueError("Total days do not add up correctly")

    # Create the trip plan
    trip_plan = [
        {'day_range': f'Day {frankfurt_start_day}-{frankfurt_end_day}', 'place': 'Frankfurt'},
        {'flying': f'Day {frankfurt_end_day}-{frankfurt_end_day}', 'from': 'Frankfurt', 'to': 'Dubrovnik'},
        {'day_range': f'Day {dubrovnik_start_day}-{dubrovnik_end_day}', 'place': 'Dubrovnik'},
        {'flying': f'Day {dubrovnik_end_day}-{dubrovnik_end_day}', 'from': 'Dubrovnik', 'to': 'Frankfurt'},
        {'day_range': f'Day {dubrovnik_end_day+1}-{dubrovnik_end_day+1}', 'place': 'Frankfurt'},
        {'flying': f'Day {dubrovnik_end_day+1}-{dubrovnik_end_day+1}', 'from': 'Frankfurt', 'to': 'Krakow'},
        {'day_range': f'Day {krakow_start_day}-{krakow_end_day}', 'place': 'Krakow'}
    ]

    return trip_plan

def main():
    krakow_days = 2
    dubrovnik_days = 7
    frankfurt_days = 1

    trip_plan = calculate_trip_plan(krakow_days, dubrovnik_days, frankfurt_days, (9, 10))
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()