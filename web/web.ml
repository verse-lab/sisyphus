open Brr


module H = Bulma.Html
module B = Bulma.Bulma(H)

let () =
  let body = Document.body G.document in
  El.append_children body  [
    B.navbar ~a_class:["is-fixed-top"] [
      B.container [
        B.navbar_brand [
          H.a [
            H.img ~a:[H.a_class ["tool-logo"]] ~src:"/res/sisyphus-logo.png" ~alt:"Sisyphus Logo (WIP)" ()
          ];
          B.navbar_burger ~a:[H.a_user_data "target" "nav-menu"] ();
        ];
        B.navbar_menu  ~a:[H.a_id "nav-menu"] ([],[
          B.navbar_item_a ~a:[H.a_href "https://github.com/verse-lab/proof-repair"] [H.txt "Source code"];
        ])
      ]
    ];

    H.section ~a:[H.a_class ["hero"; "hero-main"]] [
      H.div ~a:[H.a_class ["hero-body"]] [
        B.container [
          B.columns [
            B.column ~a_class:["is-two-fifths"] [
              H.h1 ~a:[H.a_class ["title"]] [H.txt "Automated Proof Repair"];
              H.p ~a:[H.a_class ["subtitle"]] [H.txt "made with ♥ with OCaml"]
            ];
            B.column [
              H.txt "Epic";
            ]
          ]
        ]
      ]
    ];

    El.script [
      El.txt' {|
document.addEventListener('DOMContentLoaded', () => {

  // Get all "navbar-burger" elements
  const $navbarBurgers = Array.prototype.slice.call(document.querySelectorAll('.navbar-burger'), 0);

  // Check if there are any navbar burgers
  if ($navbarBurgers.length > 0) {

    // Add a click event on each of them
    $navbarBurgers.forEach( el => {
      el.addEventListener('click', () => {

        // Get the target from the "data-target" attribute
        const target = el.dataset.target;
        const $target = document.getElementById(target);

        // Toggle the "is-active" class on both the "navbar-burger" and the "navbar-menu"
        el.classList.toggle('is-active');
        $target.classList.toggle('is-active');

      });
    });
  }

});
|}
    ]
  ]

