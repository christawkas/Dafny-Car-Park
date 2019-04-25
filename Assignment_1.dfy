
// TODO use auto contract for every method!

class CarPark {

    // Set for lots that have been reserved
    var reservedSpace: set<int>;

    // Set for ltos that dont have a reservation on them
    var generalSpace: set<int>;

    // Maximum number of cars in overall 
    var maxSpace: int;

    var maxReservedSpace: int;

    // Set of cars that have a active reservation
    var carsWRes: set<int>;

    // Boolean for parking restriction
    var parkingRestriction: bool;


    // a constructor for the class, setting the car-park up for a new day.
    //x -> size of carpark
    //y -> size of reservedSpace
    constructor (x: int, y: int)
    requires x - 8 > y
    ensures true;
    {
        maxSpace := x;
        parkingRestriction := true;

    }

    // to allow any car without a reservation to enter the car park.
    method enterCarPark (x: int) returns (res: bool)
    //ensures that car is either in generalSpace after correct execution
    ensures res ==> x in generalSpace 
    //ensures that the sum of the carpark is 1 larger after the method executes correctly
    ensures res ==> |generalSpace| == old(|generalSpace|) + 1
    //ensures that the reservedSpace carPark was not touched
    ensures old(reservedSpace) == reservedSpace
    modifies this;
    {
        //check that car does not exist in carparks and if there is free space availalbe
        if !(x in generalSpace) && !(x in reservedSpace) && |generalSpace| < maxSpace-|reservedSpace|-8 {
            generalSpace := generalSpace + {x};
            res := true; 
        } else {
            res := false;
        } 
    }

    // to allow any car from any area to leave the car park.
    // x is the id of the car
    method leaveCarPark(x: int) returns (res: bool)
    requires true;
    // ensures that car is not in the sets anymore
    ensures !(x in generalSpace && x in reservedSpace);
    modifies this;
    {
        if(x in generalSpace) {
            generalSpace := generalSpace - {x};
            res:= true;
        } else if (x in reservedSpace) {
            reservedSpace := reservedSpace - {x};
            res := true;
        } else {
            res := false;
        }
    }

    // to report on the number of non-reserved free spaces currently available.
    method checkAvailability () returns (res: int)
    requires true;
    ensures old(generalSpace) == generalSpace;
    ensures old(reservedSpace) == reservedSpace;
    {
        res := maxSpace - |generalSpace| - |reservedSpace| - 8;
    }
    
    // to allow a car with a reservation to enter the car park’s reserved area during its hours of operation, or to enter the car park generally outside these hours.
    method enterReservedCarPark (x: int) returns (res: bool)
    requires true;
    ensures res ==> old(reservedSpace) + old(generalSpace) + {x} == reservedSpace + generalSpace
    ensures res ==> old(reservedSpace) == reservedSpace || old(generalSpace) == generalSpace 
    modifies this;
    {
        if(x in carsWRes) {
            if(parkingRestriction) {
                reservedSpace :=  reservedSpace + {x};
            } else {
                generalSpace := generalSpace + {x};
            }
            res := true;
        } else {
            res := false;
        }
    }
    
    // to allow a car to be registered as having a reserved space when the owner pays the subscription.
    method makeSubscription (x: int) returns (res: bool)
    requires true;
    modifies this;
    ensures old(generalSpace) == generalSpace && old(reservedSpace) == reservedSpace
    {
        if(!(x in generalSpace || x in reservedSpace) && (|carsWRes| < maxSpace - 8) && !(x in carsWRes)){
            carsWRes := carsWRes + {x};
            res := true;
        } else {
            res := false;
        }

    }

    // to remove parking restrictions on the reserved spaces (i.e. at 3pm).
    method openReservedArea() returns ()
    ensures old(generalSpace) == generalSpace;
    ensures old(reservedSpace) == reservedSpace;
    ensures old(carsWRes) == carsWRes;
    ensures old(maxSpace) == maxSpace;
    modifies this;
    {
        parkingRestriction := false;
    }

    // to remove and crush remaining parked cars at closing time.
    method closeCarPark() returns ()
    requires true;
    ensures |generalSpace| == 0 && |reservedSpace| == 0;
    modifies this;
    {
        generalSpace := {};
        reservedSpace := {};
    }

    predicate Valid()
    reads this;
    {
        maxSpace - 8 - |generalSpace| - |reservedSpace| >= 0

    }
    method printStats() returns ()
    requires true
    ensures old(generalSpace) == generalSpace;
    ensures old(reservedSpace) == reservedSpace;
    ensures old(carsWRes) == carsWRes;
    ensures old(maxSpace) == maxSpace;
    {
        var a := generalSpace;
        var b := reservedSpace;
        var c := carsWRes;
        var s := maxSpace;

        print "Free Space", " (", maxSpace - |generalSpace| - |reservedSpace| - 8, ")", "\n";

        while ( s != 0 && 0 < s)
            decreases s;
            {
                print "[ ]", " ";
                s := s - 1;
            }
        
        

        print "\n", "\n", "General Space", " (", |generalSpace|, ")", "\n";
        while ( a != {} )
        decreases a;
        {
            var y :| y in a;
            print "[", y, "]", " ";
            a := a - { y };
        }

        print "\n", "\n", "Reserved Space", " (", |reservedSpace|, ")", "\n";
        while ( b != {} )
        decreases b;
        {
            var y :| y in b;
            print "[", y, "]", " ";
            b := b - { y };
        }

        print "\n","\n", "Reservations", "\n";
        while ( c != {} )
        decreases c;
        {
            var y :| y in c;
            print y, ", ";
            c := c - { y };
        }
    }
}
method Main ()  
{
    var cp := new CarPark(150, 20);
    var b1 := cp.makeSubscription(1);
        
    //this method call should return false
    var b2 := cp.makeSubscription(1);

    var b6 := cp.makeSubscription(6);

    var b3 := cp.enterCarPark(2);
    var b31 := cp.enterCarPark(3);
    var b311 := cp.leaveCarPark(3);
    var b32 := cp.enterCarPark(4);
    var b4 := cp.enterReservedCarPark(1);
    
    cp.printStats();

    print "\n", "\n", "#### Opening Reserved Area ####", "\n", "\n";
    cp.openReservedArea();

    var b61 := cp.enterReservedCarPark(6);
    var b7 := cp.enterCarPark(7);

    // this car has no reservation and should therefore not appear on the general space
    var b5 := cp.enterReservedCarPark(5);
    
    cp.printStats();
    
    print "\n", "\n", "#### Closing Car Park ####", "\n", "\n";
    cp.closeCarPark();

    cp.printStats();
}
