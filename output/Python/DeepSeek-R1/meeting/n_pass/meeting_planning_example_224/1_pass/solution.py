import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define travel times (in minutes)
    travel_times = {
        'Fisherman\'s Wharf': {
            'Golden Gate Park': 25,
            'Presidio': 17,
            'Richmond District': 18
        },
        'Golden Gate Park': {
            'Fisherman\'s Wharf': 24,
            'Presidio': 11,
            'Richmond District': 7
        },
        'Presidio': {
            'Fisherman\'s Wharf': 19,
            'Golden Gate Park': 12,
            'Richmond District': 7
        },
        'Richmond District': {
            'Fisherman\'s Wharf': 18,
            'Golden Gate Park': 9,
            'Presidio': 7
        }
    }

    # Convert time constraints to minutes since midnight
    start_fw = 9 * 60  # 9:00 AM

    # Melissa: Golden Gate Park, 8:30 AM to 8:00 PM
    melissa_available_start = 8 * 60 + 30  # 8:30 AM
    melissa_available_end = 20 * 60  # 8:00 PM
    melissa_min_duration = 15

    # Nancy: Presidio, 7:45 PM to 10:00 PM
    nancy_available_start = 19 * 60 + 45  # 7:45 PM
    nancy_available_end = 22 * 60  # 10:00 PM
    nancy_min_duration = 105

    # Emily: Richmond District, 4:45 PM to 10:00 PM
    emily_available_start = 16 * 60 + 45  # 4:45 PM
    emily_available_end = 22 * 60  # 10:00 PM
    emily_min_duration = 120

    # Start at Fisherman's Wharf at 9:00 AM
    current_time = start_fw

    # Travel to Golden Gate Park
    current_time += travel_times['Fisherman\'s Wharf']['Golden Gate Park']
    melissa_start = current_time  # 9:25 AM

    # Calculate latest departure from Golden Gate Park to arrive at Richmond District by 4:45 PM
    travel_to_emily = travel_times['Golden Gate Park']['Richmond District']
    latest_departure_ggp = emily_available_start - travel_to_emily
    melissa_end = latest_departure_ggp  # 4:38 PM

    # Travel to Richmond District
    current_time = melissa_end + travel_to_emily
    emily_start = current_time  # 4:45 PM
    emily_end = emily_start + emily_min_duration  # 6:45 PM

    # Travel to Presidio
    travel_to_nancy = travel_times['Richmond District']['Presidio']
    # Wait until departure time to arrive at Nancy's available start
    departure_rd = nancy_available_start - travel_to_nancy
    current_time = departure_rd + travel_to_nancy
    nancy_start = current_time  # 7:45 PM
    nancy_end = nancy_start + nancy_min_duration  # 9:30 PM

    # Build itinerary
    itinerary = [
        {
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Melissa",
            "start_time": format_time(melissa_start),
            "end_time": format_time(melissa_end)
        },
        {
            "action": "meet",
            "location": "Richmond District",
            "person": "Emily",
            "start_time": format_time(emily_start),
            "end_time": format_time(emily_end)
        },
        {
            "action": "meet",
            "location": "Presidio",
            "person": "Nancy",
            "start_time": format_time(nancy_start),
            "end_time": format_time(nancy_end)
        }
    ]

    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()