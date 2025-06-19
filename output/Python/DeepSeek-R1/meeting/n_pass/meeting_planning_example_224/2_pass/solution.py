import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
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

    start_fw = 9 * 60  # 9:00 AM

    melissa_available_end = 20 * 60  # 8:00 PM
    emily_available_start = 16 * 60 + 45  # 4:45 PM
    nancy_available_start = 19 * 60 + 45  # 7:45 PM

    min_duration_emily = 120
    min_duration_nancy = 105

    t_fw_to_ggp = travel_times['Fisherman\'s Wharf']['Golden Gate Park']
    t_ggp_to_rd = travel_times['Golden Gate Park']['Richmond District']
    t_rd_to_presidio = travel_times['Richmond District']['Presidio']

    # Start: Fisherman's Wharf at 9:00 AM
    # Travel to Golden Gate Park
    travel1_start = start_fw
    travel1_end = start_fw + t_fw_to_ggp  # 9:25 AM

    # Meet Melissa: start immediately after arrival (9:25 AM)
    melissa_start = travel1_end
    # Must leave Golden Gate Park by (Emily available start - travel time to Richmond District)
    melissa_end = emily_available_start - t_ggp_to_rd  # 16:38 PM
    melissa_duration = melissa_end - melissa_start

    # Travel from Golden Gate Park to Richmond District
    travel2_start = melissa_end
    travel2_end = travel2_start + t_ggp_to_rd  # 16:45 PM

    # Meet Emily: start immediately after arrival (16:45 PM) for 2 hours
    emily_start = travel2_end
    emily_end = emily_start + min_duration_emily  # 18:45 PM

    # Travel from Richmond District to Presidio: leave so as to arrive at 7:45 PM
    travel3_start = nancy_available_start - t_rd_to_presidio  # 19:38 PM
    travel3_end = nancy_available_start  # 19:45 PM

    # Meet Nancy: start immediately after arrival (19:45 PM) for 105 minutes
    nancy_start = travel3_end
    nancy_end = nancy_start + min_duration_nancy  # 21:30 PM

    itinerary = [
        {
            "action": "travel",
            "from": "Fisherman's Wharf",
            "to": "Golden Gate Park",
            "start_time": format_time(travel1_start),
            "end_time": format_time(travel1_end)
        },
        {
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Melissa",
            "start_time": format_time(melissa_start),
            "end_time": format_time(melissa_end)
        },
        {
            "action": "travel",
            "from": "Golden Gate Park",
            "to": "Richmond District",
            "start_time": format_time(travel2_start),
            "end_time": format_time(travel2_end)
        },
        {
            "action": "meet",
            "location": "Richmond District",
            "person": "Emily",
            "start_time": format_time(emily_start),
            "end_time": format_time(emily_end)
        },
        {
            "action": "travel",
            "from": "Richmond District",
            "to": "Presidio",
            "start_time": format_time(travel3_start),
            "end_time": format_time(travel3_end)
        },
        {
            "action": "meet",
            "location": "Presidio",
            "person": "Nancy",
            "start_time": format_time(nancy_start),
            "end_time": format_time(nancy_end)
        }
    ]

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()