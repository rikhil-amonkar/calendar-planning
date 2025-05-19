import heapq

def format_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def to_minutes(time_str):
    hours, mins = map(int, time_str.split(':'))
    return hours * 60 + mins

# Read travel times
travel_times = {
    'Russian Hill': {
        'Pacific Heights': 7,
    },
    'Pacific Heights': {
        'Russian Hill': 7,
    }
}

# Read people data and convert times to minutes
people = [
    {
        'name': 'Barbara',
        'location': 'Pacific Heights',
        'availability_start': '7:15',
        'availability_end': '22:00',
        'required_time': 60
    }
]

for person in people:
    person['availability_start'] = to_minutes(person['availability_start'])
    person['availability_end'] = to_minutes(person['availability_end'])

# Initialize priority queue
priority_queue = []

for person in people:
    from_loc = 'Russian Hill'
    to_loc = person['location']
    arrival_time = 540 + travel_times[from_loc][to_loc]
    avail_start = person['availability_start']
    avail_end = person['availability_end']
    required = person['required_time']
    
    earliest_start = max(arrival_time, avail_start)
    latest_start = avail_end - required
    
    if earliest_start <= latest_start:
        heapq.heappush(priority_queue, (earliest_start, earliest_start + required, person))

schedule = []
current_end = 540  # 9:00 AM in minutes

while priority_queue:
    start_min, end_min, person = heapq.heappop(priority_queue)
    
    # Check if this meeting can be scheduled
    if start_min >= current_end:
        # Check if the meeting ends before the person's availability end
        if end_min <= person['availability_end']:
            # Add to schedule
            schedule.append({
                'action': 'meet',
                'location': person['location'],
                'person': person['name'],
                'start_time': format_time(start_min),
                'end_time': format_time(end_min)
            })
            current_end = end_min
            
            # Check for more possible meetings
            for p in people:
                from_loc = 'Russian Hill'
                to_loc = p['location']
                arrival_time = 540 + travel_times[from_loc][to_loc]
                avail_start = p['availability_start']
                avail_end = p['availability_end']
                required = p['required_time']
                
                earliest_start = max(arrival_time, avail_start)
                latest_start = avail_end - required
                
                if earliest_start <= latest_start:
                    if earliest_start >= current_end:
                        heapq.heappush(priority_queue, (earliest_start, earliest_start + required, p))
    else:
        # This meeting can't be scheduled now, put it back into the queue
        heapq.heappush(priority_queue, (start_min, end_min, person))

# Convert the schedule to the required format
itinerary = []
for meeting in schedule:
    location = meeting['location']
    person = meeting['person']
    start = meeting['start_time']
    end = meeting['end_time']
    itinerary.append({
        'action': 'meet',
        'location': location,
        'person': person,
        'start_time': start,
        'end_time': end
    })

# Convert itinerary to JSON
import json
print(json.dumps({
    "itinerary": itinerary
}))