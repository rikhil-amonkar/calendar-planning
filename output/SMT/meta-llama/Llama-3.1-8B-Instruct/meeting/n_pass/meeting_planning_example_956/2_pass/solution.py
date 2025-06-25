for i in range(len(friends)):
    friend = friends[i]
    start_time_friend = friend_times[friend][0]
    end_time_friend = friend_times[friend][1]
    meeting_time_friend = friend_meeting_times[friend]
    location_friend = friend_locations[friend]
    location_meeting = locations[0]  # Initialize to The Castro
    for j in range(len(locations)):
        s.add(And(meetings[j * len(locations) + locations.index(location_friend)], 
                  And(start_time + stay_times_var[j * len(locations)] <= start_time_friend + meeting_time_friend, 
                      end_time_friend - meeting_time_friend <= start_time + stay_times_var[j * len(locations)] + travel_times_var[j * len(locations) + locations.index(location_meeting)])))
    s.add(Or([meetings[k * len(locations) + locations.index(location_friend)] for k in range(len(locations))]))