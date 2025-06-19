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
            'Fisherman\'s Wharf': 25,
            'Presidio': 11,
            'Richmond District': 9
        },
        'Presidio': {
            'Fisherman\'s Wharf': 17,
            'Golden Gate Park': 11,
            'Richmond District': 7
        },
        'Richmond District': {
            'Fisherman\'s Wharf': 18,
            'Golden Gate Park': 9,
            'Presidio': 7
        }
    }

    start_fw = 9 * 60  # 9:00 AM

    # Travel from Fisherman's Wharf to Golden Gate Park
    travel1_start = start_fw
    travel1_end = start_fw + travel_times['Fisherman\'s Wharf']['Golden Gate Park']  # 9:25

    # Meet Melissa starts immediately after arrival
    melissa_start = travel1_end  # 9:25

    # Calculate latest departure time from Golden Gate Park
    nancy_available_start = 19 * 60 + 45  # 7:45 PM
    travel_rd_to_presidio = travel_times['Richmond District']['Presidio']  # 7 min
    min_duration_emily = 120  # 2 hours
    
    # Latest time to leave Richmond District to reach Presidio by 7:45 PM
    leave_rd_by = nancy_available_start - travel_rd_to_presidio  # 19:38
    # Emily meeting must start by this time to complete 2 hours
    emily_start_by = leave_rd_by - min_duration_emily  # 17:38
    # Travel time from Golden Gate Park to Richmond District
    travel_ggp_to_rd = travel_times['Golden Gate Park']['Richmond District']  # 9 min
    # Latest departure time from Golden Gate Park
    leave_ggp_by = emily_start_by - travel_ggp_to_rd  # 17:29

    melissa_end = leave_ggp_by  # 17:29

    # Travel from Golden Gate Park to Richmond District
    travel2_start = melissa_end  # 17:29
    travel2_end = travel2_start + travel_ggp_to_rd  # 17:38

    # Meet Emily for exactly 2 hours
    emily_start = travel2_end  # 17:38
    emily_end = emily_start + min_duration_emily  # 19:38

    # Travel to Presidio
    travel3_start = emily_end  # 19:38
    travel3_end = travel3_start + travel_rd_to_presidio  # 19:45

    # Meet Nancy for at least 105 minutes
    min_duration_nancy = 105
    nancy_start = travel3_end  # 19:45
    nancy_end = nancy_start + min_duration_nancy  # 21:30

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