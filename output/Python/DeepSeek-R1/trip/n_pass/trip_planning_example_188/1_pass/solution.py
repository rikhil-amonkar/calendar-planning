import json

def main():
    total_days = 12
    brussels_days = 2
    split_days = 5
    barcelona_days = 7

    brussels_start = 1
    brussels_end = brussels_start + brussels_days - 1

    barcelona_start = brussels_end
    barcelona_end = barcelona_start + barcelona_days - 1

    split_start = barcelona_end
    split_end = split_start + split_days - 1

    itinerary = [
        {"day_range": f"Day {brussels_start}-{brussels_end}", "place": "Brussels"},
        {"day_range": f"Day {barcelona_start}-{barcelona_end}", "place": "Barcelona"},
        {"day_range": f"Day {split_start}-{split_end}", "place": "Split"}
    ]

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()