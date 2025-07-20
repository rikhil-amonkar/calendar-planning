import json

def main():
    fixed_segments = [
        (1, 4, "Mykonos"),
        (11, 15, "Dublin"),
        (15, 17, "Frankfurt")
    ]
    
    segments = []
    
    gap1_cities = ["Naples", "Istanbul", "Venice"]
    gap1_durations = [4, 3, 3]
    start = 4
    for i in range(len(gap1_cities)):
        end = start + gap1_durations[i] - 1
        segments.append((start, end, gap1_cities[i]))
        start = end
    
    gap2_cities = ["Krakow", "Brussels"]
    gap2_durations = [4, 2]
    start = 17
    for i in range(len(gap2_cities)):
        end = start + gap2_durations[i] - 1
        segments.append((start, end, gap2_cities[i]))
        start = end
    
    all_segments = fixed_segments + segments
    sorted_segments = sorted(all_segments, key=lambda x: x[0])
    
    itinerary_list = []
    for seg in sorted_segments:
        s, e, city = seg
        if s == e:
            day_range = f"Day {s}"
        else:
            day_range = f"Day {s}-{e}"
        itinerary_list.append({"day_range": day_range, "place": city})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == '__main__':
    main()